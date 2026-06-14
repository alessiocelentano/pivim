/**
 * Vim modal editor extension for Pi.
 *
 * Modes:  INSERT · NORMAL · VISUAL (char/line) · COMMAND
 *
 * Neovim-inspired operator+motion architecture:
 *   Operators:  d (delete), c (change), y (yank), > (indent), < (outdent)
 *   Motions:    h j k l  w b e W B E  0 ^ $  G gg  f F t T  % { }
 *   Line ops:   dd cc yy >> << (double-tap)
 *   Text objs:  iw aw i( a( i" a"  ib ab  i{ a{  i[ a[  i< a<
 *   Registers:  "a .. "z prefix (used by d/c/y + p/P put)
 *   Macros:     q<reg> record, q stop, @<reg> play
 *   Join:       J (like Neovim: at cursor, with insert_space)
 *   Man page:   :man opens the man page in less
 *   Undo/Redo:  u / Ctrl+R
 *   Visual:     v (char), V (line) with d/c/y operators
 *   Commands:   :w save, :wq save+quit, :q quit, :q! quit, :!<cmd> bash,
 *               :s/old/new[/flags] substitute
 *   Search:     / forward, ? backward, n/N repeat, * (word search), # (word search)
 *   Y = yy      (linewise yank, like Neovim)
 *   C = c$      (change to end of line)
 *   s = cl      (substitute char)
 *   S = cc      (substitute line)
 *   .           repeat last change
 *   Empty-line stops: w/b stop on blank lines (Neovim semantics)
 *
 * Status bar widget shows: mode label, pending count, cursor position,
 * recording indicator, and command buffer.
 */

import { CustomEditor, type ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { matchesKey, visibleWidth, Key, wrapTextWithAnsi } from "@earendil-works/pi-tui";
import type { TUI } from "@earendil-works/pi-tui";
import * as fs from "fs";
import * as path from "path";
import * as os from "os";
import { execSync } from "child_process";

// ─────────────────────────────────────────────────────────────
// Types
// ─────────────────────────────────────────────────────────────

type Mode = "INSERT" | "NORMAL" | "VISUAL" | "COMMAND";
type VisualType = "char" | "line";
type Operator = "d" | "c" | "y" | ">" | "<";

/** Macro registers: each register holds a sequence of keystrokes. */
interface MacroRegisters { [r: string]: string[] }

/** Serialized prompt state for :w / :wq / resume. */
interface SavedState { text: string; cursorLine: number; cursorCol: number; }

/** Undo/redo entry: full text + cursor position. */
interface UndoEntry { text: string; line: number; col: number; }

/** Last change record for the '.' repeat operator. */
interface LastChange {
  type: "simple" | "lineOp" | "charRange" | "visual";
  op: Operator;
  count: number;
  // For charRange:
  startLine?: number; startCol?: number; endLine?: number; endCol?: number;
  inclusive?: boolean;
  // For lineOp:
  startLineOp?: number; endLineOp?: number;
  // For visual:
  visualType?: VisualType;
  visualStartLine?: number; visualStartCol?: number;
  visualEndLine?: number; visualEndCol?: number;
}

// ─────────────────────────────────────────────────────────────
// Shared state (editor → status-bar widget bridge)
// ─────────────────────────────────────────────────────────────

const vimState = {
  mode: "INSERT" as Mode,
  line: 1, totalLines: 1, col: 1,
  recording: false as string | false,
  commandBuffer: "",
  pendingCount: "",
};

// ─────────────────────────────────────────────────────────────
// VimEditor
// ─────────────────────────────────────────────────────────────

/** Pi state file path for :w / :wq / resume. */
const STATE_PATH = path.join(os.homedir(), ".pi_vim_save.json");

/** Bracket pairs for % matching. */
const BRACKET_PAIRS: Record<string, string> = {
  "(": ")", ")": "(",
  "[": "]", "]": "[",
  "{": "}", "}": "{",
  "<": ">", ">": "<",
};

class VimEditor extends CustomEditor {
  // ── Mode ──
  private _mode: Mode = "INSERT";
  private _prevMode: Mode = "INSERT";

  // ── Operator state ──
  private pendingOp: Operator | null = null;

  // ── Count accumulator ──
  private countBuf = "";

  // ── Register prefix ──
  private registerName = "";

  // ── Yank register ──
  private yankBuffer = "";
  private yankType: "char" | "line" = "char";

  // ── Undo/Redo ──
  private vimUndoStack: UndoEntry[] = [];
  private vimRedoStack: UndoEntry[] = [];

  /** Save the current text AND cursor for undo BEFORE an editing operation. */
  private saveUndoState() {
    const c = this.getCursor();
    this.vimUndoStack.push({ text: this.getText(), line: c.line, col: c.col });
    this.vimRedoStack.length = 0;
  }

  // ── Last change (for . repeat) ──
  private lastChange: LastChange | null = null;

  // ── Pending second key for g*, z*, f/F/t/T, text objects (i/a), r, q, @, " ──
  private pendingLeader: string | null = null;

  // ── Text-object modifier (set when 'i' or 'a' is pressed after an operator) ──
  private textObjMod: "i" | "a" | null = null;

  // ── Macros ──
  private macroRegs: MacroRegisters = {};
  private _recording: string | false = false;

  // ── Visual ──
  private visualStartLine = -1;
  private visualStartCol = -1;
  private _visualType: VisualType = "char";

  // ── Last visual selection (for gv and '.' repeat) ──
  private lastVisualStartLine = -1;
  private lastVisualStartCol = -1;
  private lastVisualEndLine = -1;
  private lastVisualEndCol = -1;
  private lastVisualType: VisualType = "char";

  // ── Search state ──
  private lastSearchDir: "/" | "?" = "/";
  private lastSearchPattern = "";

  // ── Command-line buffer ──
  commandBuffer = "";

  // ── TUI ref ──
  private tuiRef: TUI;

  // ── DECSCUSR cursor shapes ──
  private static readonly DECSCUSR: Record<string, string> = {
    INSERT:  "\x1b[6 q",
    NORMAL:  "\x1b[2 q",
    VISUAL:  "\x1b[4 q",
    COMMAND: "\x1b[6 q",
  };

  // Callback for graceful shutdown (set by extension setup)
  public onQuit?: () => void;

  constructor(tui: TUI, theme: any, kb: any, opts?: any) {
    super(tui, theme, kb, opts);
    this.tuiRef = tui;
    this.tuiRef.setShowHardwareCursor(true);
    this.tuiRef.terminal.write(VimEditor.DECSCUSR["INSERT"]);
  }

  // ───────────────────────────────────────────────────────────
  // Mode transitions
  // ───────────────────────────────────────────────────────────

  private get mode(): Mode { return this._mode; }
  private set mode(m: Mode) {
    if (this._mode === m) return;
    this._prevMode = this._mode;
    this._mode = m;
    this.pendingOp = null;
    this.pendingLeader = null;
    this.textObjMod = null;
    this.countBuf = "";
    this.registerName = "";
    if (m !== "COMMAND") {
      this.commandBuffer = "";
    }

    if (m === "VISUAL") {
      const c = this.getCursor();
      this.visualStartLine = c.line;
      this.visualStartCol = c.col;
    }

    if (m === "NORMAL") {
      if (this._prevMode === "INSERT") {
        const c = this.getCursor();
        if (c.col > 0) super.handleInput("\x1b[D");
      }
      this.clampNormalCursor();
    }

    this.tuiRef.terminal.write(VimEditor.DECSCUSR[m]);
    this.syncState();
    this.tuiRef.requestRender();
  }

  private clampNormalCursor() {
    const c = this.getCursor();
    const line = this.getLines()[c.line] ?? "";
    if (c.col > 0 && c.col >= line.length && line.length > 0) {
      super.handleInput("\x1b[D");
    }
  }

  private syncState() {
    const c = this.getCursor();
    vimState.mode = this._mode;
    vimState.line = c.line + 1;
    vimState.totalLines = this.getLines().length;
    vimState.col = c.col + 1;
    vimState.recording = this._recording;
    vimState.commandBuffer = this.commandBuffer;
    vimState.pendingCount = this.countBuf;
  }

  // ───────────────────────────────────────────────────────────
  // Helpers
  // ───────────────────────────────────────────────────────────

  private getCursorCol0(): number { return this.getCursor().col; }
  private getCursorLine0(): number { return this.getCursor().line; }
  private lineCount(): number { return this.getLines().length; }
  private lineAt(i: number): string { return this.getLines()[i] ?? ""; }

  private isDigit(ch: string): boolean {
    return ch.length === 1 && ch >= "0" && ch <= "9";
  }

  private consumeCount(defaultVal: number = 1): number {
    const raw = this.countBuf;
    this.countBuf = "";
    if (!raw) return defaultVal;
    const n = Number.parseInt(raw, 10);
    if (!Number.isFinite(n) || n <= 0) return defaultVal;
    return Math.min(9999, n);
  }

  private cursorLineEmpty(): boolean {
    return this.lineAt(this.getCursorLine0()).trimEnd() === "";
  }

  // ───────────────────────────────────────────────────────────
  // Undo/Redo helpers
  // ───────────────────────────────────────────────────────────

  private undoOne() {
    const entry = this.vimUndoStack.pop();
    if (entry !== undefined) {
      const c = this.getCursor();
      this.vimRedoStack.push({ text: this.getText(), line: c.line, col: c.col });
      this.setText(entry.text);
      this.gotoAbs(entry.line, entry.col);
    }
  }

  private redoOne() {
    const entry = this.vimRedoStack.pop();
    if (entry !== undefined) {
      const c = this.getCursor();
      this.vimUndoStack.push({ text: this.getText(), line: c.line, col: c.col });
      this.setText(entry.text);
      this.gotoAbs(entry.line, entry.col);
    }
  }

  // ───────────────────────────────────────────────────────────
  // Macros
  // ───────────────────────────────────────────────────────────

  private startRecording(reg: string) {
    this._recording = reg;
    this.macroRegs[reg] = [];
    this.syncState();
    this.tuiRef.requestRender();
  }

  private stopRecording() {
    this._recording = false;
    this.syncState();
    this.tuiRef.requestRender();
  }

  private playMacro(reg: string) {
    const keys = this.macroRegs[reg];
    if (!keys) return;
    for (const k of keys) this.handleInput(k);
  }

  private recordKey(data: string) {
    if (typeof this._recording === "string") {
      this.macroRegs[this._recording].push(data);
    }
  }

  // ───────────────────────────────────────────────────────────
  // Navigate to absolute 0-based position
  // ───────────────────────────────────────────────────────────

  private goToLineAbs(target: number) {
    const n = this.lineCount();
    const t = Math.max(0, Math.min(target, n - 1));
    const diff = t - this.getCursorLine0();
    if (diff > 0) {
      for (let i = 0; i < diff; i++) super.handleInput("\x1b[B");
    } else if (diff < 0) {
      for (let i = 0; i < -diff; i++) super.handleInput("\x1b[A");
    }
    super.handleInput("\x01"); // home
  }

  // ───────────────────────────────────────────────────────────
  // Motion helpers
  // ───────────────────────────────────────────────────────────

  private motionLeft(n: number)  { for (let i=0;i<n;i++) super.handleInput("\x1b[D"); }
  private motionRight(n: number) { for (let i=0;i<n;i++) super.handleInput("\x1b[C"); }
  private motionUp(n: number)    {
    const curLine = this.getCursorLine0();
    const maxSteps = Math.min(n, curLine);
    for (let i = 0; i < maxSteps; i++) super.handleInput("\x1b[A");
  }
  private motionDown(n: number)  {
    const curLine = this.getCursorLine0();
    const maxSteps = Math.min(n, this.lineCount() - 1 - curLine);
    for (let i = 0; i < maxSteps; i++) super.handleInput("\x1b[B");
  }
  private motionHome()           { super.handleInput("\x01"); }
  private motionEnd()            { super.handleInput("\x05"); }

  private motionDollar() {
    this.motionEnd();
    if (!this.cursorLineEmpty()) this.motionLeft(1);
  }

  private motionFirstNonBlank() {
    this.motionHome();
    const line = this.lineAt(this.getCursorLine0());
    let i = 0;
    while (i < line.length && (line[i] === " " || line[i] === "\t")) i++;
    if (i > 0) this.motionRight(i);
  }

  private static isWordChar(ch: string): boolean { return /[a-zA-Z0-9_]/.test(ch); }
  private static isNonBlank(ch: string): boolean { return !/\s/.test(ch); }

  private gotoAbs(line: number, col: number) {
    this.goToLineAbs(line);
    this.motionHome();
    if (col > 0) this.motionRight(col);
  }

  // ───────────────────────────────────────────────────────────
  // Word motions (rewritten: simpler & closer to Neovim)
  // ───────────────────────────────────────────────────────────

  /**
   * Move forward `count` words (w / W).
   * In word-motion, ~ is a non-word separator (standard Vim iskeyword).
   */
  private motionWordForward(count: number, bigWord: boolean, eol: boolean) {
    const isWord = bigWord ? VimEditor.isNonBlank : VimEditor.isWordChar;
    const lines = this.getLines();
    let line = this.getCursorLine0();
    let col = this.getCursorCol0();
    const maxLine = lines.length - 1;

    for (let i = 0; i < count && line <= maxLine; i++) {
      const curLine = lines[line] ?? "";
      // Are we on a word char?
      const onWord = col < curLine.length && isWord(curLine[col]);

      // Step forward one character
      if (col < curLine.length) {
        col++;
      } else if (line < maxLine) {
        line++; col = 0;
        if (eol && i === count - 1) break; // eol stop
      } else {
        col = curLine.length; break;
      }

      if (onWord) {
        // Skip to end of this word
        while (line <= maxLine) {
          const ln = lines[line] ?? "";
          while (col < ln.length && isWord(ln[col])) col++;
          if (col < ln.length || line >= maxLine) break;
          if (eol && i === count - 1) break;
          line++; col = 0;
        }
      }

      // Now skip non-word chars to find next word start
      while (line <= maxLine) {
        const ln = lines[line] ?? "";
        if (col === 0 && ln.length === 0 && i < count - 1) {
          // Blank line: skip it (Neovim: stop on blank lines)
          if (line < maxLine) { line++; col = 0; continue; }
        }
        while (col < ln.length && !isWord(ln[col])) col++;
        if (col < ln.length) break; // found word char
        if (line >= maxLine) { col = ln.length; break; }
        if (eol && i === count - 1) break;
        line++; col = 0;
        // Stop on blank line
        if ((lines[line] ?? "").length === 0) {
          col = 0; break;
        }
      }
    }

    if (line > maxLine) { line = maxLine; col = (lines[maxLine] ?? "").length; }
    else if (col > (lines[line] ?? "").length) col = (lines[line] ?? "").length;
    this.gotoAbs(line, col);
  }

  private motionWordBackward(count: number, bigWord: boolean) {
    const isWord = bigWord ? VimEditor.isNonBlank : VimEditor.isWordChar;
    const lines = this.getLines();
    let line = this.getCursorLine0();
    let col = this.getCursorCol0();

    for (let i = 0; i < count && line >= 0; i++) {
      // Step back one char
      if (col > 0) {
        col--;
      } else if (line > 0) {
        line--;
        col = (lines[line] ?? "").length - 1;
        if (col < 0) col = 0;
      } else {
        col = 0; break;
      }

      // Skip non-word chars going backward
      while (line >= 0) {
        const ln = lines[line] ?? "";
        if (col === 0 && ln.length === 0) {
          if (line > 0) { line--; col = (lines[line] ?? "").length - 1; continue; }
          break;
        }
        if (col >= ln.length) col = ln.length - 1;
        if (col < 0) break;
        if (isWord(ln[col])) break;
        if (col > 0) { col--; }
        else if (line > 0) { line--; col = (lines[line] ?? "").length - 1; }
        else break;
      }
      if (line < 0) break;

      // Skip to start of word (going backward)
      while (col > 0 && isWord((lines[line] ?? "")[col - 1] ?? "")) col--;
    }

    if (line < 0) { line = 0; col = 0; }
    this.gotoAbs(line, col);
  }

  /**
   * Move to end of `count`-th word forward (e / E). Inclusive.
   */
  private motionWordEnd(count: number, bigWord: boolean) {
    const isWord = bigWord ? VimEditor.isNonBlank : VimEditor.isWordChar;
    const lines = this.getLines();
    let line = this.getCursorLine0();
    let col = this.getCursorCol0();
    const maxLine = lines.length - 1;

    for (let i = 0; i < count && line <= maxLine; i++) {
      // Step forward one
      if (col < (lines[line] ?? "").length) {
        col++;
      } else if (line < maxLine) {
        line++; col = 0;
      } else {
        col = (lines[line] ?? "").length; break;
      }

      const curLine = lines[line] ?? "";
      const onWord = col < curLine.length && isWord(curLine[col]);

      if (onWord) {
        // Skip to end of this word
        while (col < curLine.length && isWord(curLine[col])) col++;
      } else {
        // Skip non-word to find next word start
        while (line <= maxLine) {
          const ln = lines[line] ?? "";
          while (col < ln.length && !isWord(ln[col])) col++;
          if (col < ln.length) break;
          if (line >= maxLine) { col = ln.length; break; }
          line++; col = 0;
          if ((lines[line] ?? "").length === 0) { col = 0; break; }
        }
        if (line > maxLine) { line = maxLine; col = (lines[maxLine] ?? "").length; break; }
        // Skip to end of this word
        while (line <= maxLine) {
          const ln = lines[line] ?? "";
          while (col < ln.length && isWord(ln[col])) col++;
          if (col < ln.length) break;
          if (line >= maxLine) { col = ln.length; break; }
          line++; col = 0;
          if ((lines[line] ?? "").length === 0 || !isWord((lines[line] ?? "")[0] ?? "")) break;
        }
      }

      // e is inclusive: go back one char
      if (col > 0) {
        col--;
      } else if (line > 0) {
        line--;
        col = Math.max(0, (lines[line] ?? "").length - 1);
      }
    }

    if (line > maxLine) { line = maxLine; col = (lines[maxLine] ?? "").length; }
    this.gotoAbs(line, Math.max(0, col));
  }

  // ───────────────────────────────────────────────────────────
  // Paragraph motions: { and }
  // ───────────────────────────────────────────────────────────

  /**
   * Jump to previous paragraph start (blank line).
   * Neovim findpar semantics: must pass through non-blank content first
   * (the current paragraph), then stop at the next blank line.
   * Cursor ends at column 0.
   */
  private motionPrevParagraph(count: number) {
    const lines = this.getLines();
    let line = this.getCursorLine0();

    for (let i = 0; i < count; i++) {
      let didSkip = false;
      for (let first = true; ; first = false) {
        if (lines[line] !== "") didSkip = true;
        if (!first && didSkip && lines[line].trimEnd() === "") break;
        line--;
        if (line < 0) {
          if (i < count - 1) return;
          line = 0;
          break;
        }
      }
    }
    this.goToLineAbs(line);
    // Neovim: cursor at col 0 (not first non-blank)
  }

  /**
   * Jump to next paragraph start (blank line).
   * Neovim findpar semantics: must pass through non-blank content first,
   * then stop at the next blank line. Cursor ends at column 0 (or last
   * char of last line if at end of file).
   */
  private motionNextParagraph(count: number) {
    const lines = this.getLines();
    let line = this.getCursorLine0();
    const maxLine = lines.length - 1;

    for (let i = 0; i < count; i++) {
      let didSkip = false;
      for (let first = true; ; first = false) {
        if (lines[line] !== "") didSkip = true;
        if (!first && didSkip && lines[line].trimEnd() === "") break;
        line++;
        if (line > maxLine) {
          if (i < count - 1) return;
          line = maxLine;
          break;
        }
      }
    }
    this.goToLineAbs(line);
    // Neovim: cursor at col 0 (not first non-blank)
  }

  // ───────────────────────────────────────────────────────────
  // Bracket matching: %
  // ───────────────────────────────────────────────────────────

  /**
   * % motion: find matching bracket.
   * Neovim-inspired: if cursor is on a bracket, match it (multi-line).
   * If cursor is not on a bracket, scan forward on the current line for
   * the next bracket and then match it.
   */
  private motionPercent() {
    const lines = this.getLines();
    const curLine = this.getCursorLine0();
    const curCol = this.getCursorCol0();
    const line = lines[curLine] ?? "";
    const maxLine = lines.length - 1;

    let ch = curCol < line.length ? line[curCol] : "";
    let matching = BRACKET_PAIRS[ch];
    let searchCol = curCol;

    if (!matching) {
      // Cursor not on a bracket: scan forward on current line for one.
      for (let col = curCol; col < line.length; col++) {
        const c = line[col];
        if (BRACKET_PAIRS[c]) {
          ch = c;
          matching = BRACKET_PAIRS[c];
          searchCol = col;
          break;
        }
      }
    }

    if (!matching) return; // No bracket found on the line

    // Determine direction: if it's an opening bracket, go forward; else backward
    const isOpen = "([{<".includes(ch);
    const target = matching;

    let depth = 0;

    if (isOpen) {
      // Forward search from the bracket position
      let ln = curLine;
      let col = searchCol;
      while (ln <= maxLine) {
        const lnText = lines[ln] ?? "";
        while (col < lnText.length) {
          const c = lnText[col];
          if (c === ch) depth++;
          else if (c === target) {
            depth--;
            if (depth === 0) {
              this.gotoAbs(ln, col);
              return;
            }
          }
          col++;
        }
        ln++; col = 0;
      }
    } else {
      // Backward search from the bracket position
      let ln = curLine;
      let col = searchCol;
      while (ln >= 0) {
        const lnText = lines[ln] ?? "";
        while (col >= 0) {
          const c = lnText[col] ?? "";
          if (c === ch) depth++;
          else if (c === target) {
            depth--;
            if (depth === 0) {
              this.gotoAbs(ln, col);
              return;
            }
          }
          col--;
        }
        ln--; col = (lines[ln] ?? "").length - 1;
      }
    }
  }

  // ───────────────────────────────────────────────────────────
  // Screen jumps: H, M, L
  // ───────────────────────────────────────────────────────────

  /** Get the range of visible visual lines. */
  private getVisibleRange(): { firstVisual: number; lastVisual: number; totalVisual: number } {
    const visualMap = (this as any).buildVisualLineMap?.() as Array<{logicalLine: number; startCol: number; length: number}> | undefined;
    const scrollOff: number = (this as any).scrollOffset ?? 0;
    const terminalHeight = this.tuiRef.terminal.rows;
    const topBorder = 1;
    const statusHeight = 1;
    const editorHeight = terminalHeight - topBorder - statusHeight;

    if (!visualMap || visualMap.length === 0) {
      return { firstVisual: 0, lastVisual: 0, totalVisual: 0 };
    }
    const totalVisual = visualMap.length;
    const firstVisual = scrollOff;
    const lastVisual = Math.min(scrollOff + editorHeight - 1, totalVisual - 1);
    return { firstVisual, lastVisual, totalVisual };
  }

  /** Jump to top of visible screen (H). */
  private motionScreenTop(count: number) {
    const { firstVisual } = this.getVisibleRange();
    const visualMap = (this as any).buildVisualLineMap?.() as Array<{logicalLine: number; startCol: number; length: number}>;
    if (!visualMap) return;
    const targetVis = Math.min(firstVisual + Math.max(0, count - 1), visualMap.length - 1);
    const info = visualMap[targetVis];
    if (info) {
      this.gotoAbs(info.logicalLine, info.startCol);
      this.motionFirstNonBlank();
    }
  }

  /** Jump to middle of visible screen (M). */
  private motionScreenMiddle() {
    const { firstVisual, lastVisual } = this.getVisibleRange();
    const visualMap = (this as any).buildVisualLineMap?.() as Array<{logicalLine: number; startCol: number; length: number}>;
    if (!visualMap) return;
    const midVis = Math.floor((firstVisual + lastVisual) / 2);
    const info = visualMap[Math.max(0, Math.min(midVis, visualMap.length - 1))];
    if (info) {
      this.gotoAbs(info.logicalLine, info.startCol);
      this.motionFirstNonBlank();
    }
  }

  /** Jump to bottom of visible screen (L). */
  private motionScreenBottom(count: number) {
    const { lastVisual } = this.getVisibleRange();
    const visualMap = (this as any).buildVisualLineMap?.() as Array<{logicalLine: number; startCol: number; length: number}>;
    if (!visualMap) return;
    const targetVis = Math.max(0, lastVisual - Math.max(0, count - 1));
    const info = visualMap[targetVis];
    if (info) {
      this.gotoAbs(info.logicalLine, info.startCol);
      this.motionFirstNonBlank();
    }
  }

  // ───────────────────────────────────────────────────────────
  // Page scroll: Ctrl+F, Ctrl+B
  // ───────────────────────────────────────────────────────────

  private pageDown() {
    const pageScroll = (this as any).pageScroll as ((dir: 1 | -1) => void) | undefined;
    if (pageScroll) pageScroll(1);
  }

  private pageUp() {
    const pageScroll = (this as any).pageScroll as ((dir: 1 | -1) => void) | undefined;
    if (pageScroll) pageScroll(-1);
  }

  // ───────────────────────────────────────────────────────────
  // Scroll cursor: zt, zz, zb
  // ───────────────────────────────────────────────────────────

  /** Scroll so cursor is at top of visible area. */
  private scrollCursorTop() {
    const visualMap = (this as any).buildVisualLineMap?.() as Array<{logicalLine: number; startCol: number; length: number}> | undefined;
    if (!visualMap) return;
    const curLine = this.getCursorLine0();
    // Find the first visual line corresponding to curLine
    let visIdx = 0;
    for (let i = 0; i < visualMap.length; i++) {
      if (visualMap[i].logicalLine >= curLine) { visIdx = i; break; }
    }
    const scrollOff: number = (this as any).scrollOffset ?? 0;
    if (visIdx !== scrollOff) {
      (this as any).scrollOffset = visIdx;
      this.clampNormalCursor();
    }
    this.tuiRef.requestRender();
  }

  /** Scroll so cursor is at center of visible area. */
  private scrollCursorMiddle() {
    const visualMap = (this as any).buildVisualLineMap?.() as Array<{logicalLine: number; startCol: number; length: number}> | undefined;
    if (!visualMap) return;
    const curLine = this.getCursorLine0();
    let visIdx = 0;
    for (let i = 0; i < visualMap.length; i++) {
      if (visualMap[i].logicalLine >= curLine) { visIdx = i; break; }
    }
    const terminalHeight = this.tuiRef.terminal.rows;
    const editorHeight = terminalHeight - 2; // top border + status
    const half = Math.floor(editorHeight / 2);
    const target = Math.max(0, visIdx - half);
    const maxScroll = Math.max(0, visualMap.length - editorHeight);
    (this as any).scrollOffset = Math.min(target, maxScroll);
    this.clampNormalCursor();
    this.tuiRef.requestRender();
  }

  /** Scroll so cursor is at bottom of visible area. */
  private scrollCursorBottom() {
    const visualMap = (this as any).buildVisualLineMap?.() as Array<{logicalLine: number; startCol: number; length: number}> | undefined;
    if (!visualMap) return;
    const curLine = this.getCursorLine0();
    let visIdx = 0;
    for (let i = 0; i < visualMap.length; i++) {
      if (visualMap[i].logicalLine >= curLine) { visIdx = i; break; }
    }
    const terminalHeight = this.tuiRef.terminal.rows;
    const editorHeight = terminalHeight - 2;
    const target = Math.max(0, visIdx - editorHeight + 1);
    const maxScroll = Math.max(0, visualMap.length - editorHeight);
    (this as any).scrollOffset = Math.min(target, maxScroll);
    this.clampNormalCursor();
    this.tuiRef.requestRender();
  }

  // ───────────────────────────────────────────────────────────
  // Delete helpers
  // ───────────────────────────────────────────────────────────

  private deleteCharRightChars(n: number) {
    for (let i = 0; i < n; i++) super.handleInput("\x1b[3~");
  }
  private deleteCharLeft(n: number) {
    for (let i = 0; i < n; i++) super.handleInput("\x7f");
  }
  private deleteToEnd() { super.handleInput("\x0b"); }
  private deleteToStart() { super.handleInput("\x15"); }

  private deleteLine() {
    this.saveUndoState();
    const text = this.getText();
    const lines = text.split("\n");
    const cur = this.getCursorLine0();
    if (lines.length <= 1) {
      this.setText("");
      this.goToLineAbs(0);
      this.motionHome();
    } else {
      lines.splice(cur, 1);
      this.setText(lines.join("\n"));
      const target = Math.min(cur, lines.length - 1);
      this.goToLineAbs(target);
      this.motionFirstNonBlank();
    }
    this.recordLastChange("lineOp", "d", 1, { startLineOp: cur, endLineOp: cur });
  }

  private deleteLineRange(start: number, end: number) {
    const text = this.getText();
    const lines = text.split("\n");
    const s = Math.max(0, Math.min(start, end));
    const e = Math.min(lines.length - 1, Math.max(start, end));
    const count = e - s + 1;
    if (count <= 0) return;

    if (s === 0 && count >= lines.length) {
      this.setText("");
      this.goToLineAbs(0);
      this.motionHome();
    } else {
      lines.splice(s, count);
      if (lines.length === 0) lines.push("");
      this.setText(lines.join("\n"));
      const target = Math.min(s, lines.length - 1);
      this.goToLineAbs(target);
      this.motionFirstNonBlank();
    }
  }

  private deleteCrossLineRange(startLine: number, startCol: number, endLine: number, endCol: number) {
    const text = this.getText();
    const lines = text.split("\n");
    if (startLine === endLine) {
      const line = lines[startLine] ?? "";
      const a = Math.min(startCol, endCol);
      const b = Math.min(Math.max(startCol, endCol), line.length - 1);
      if (b < a || a >= line.length) return;
      lines[startLine] = line.slice(0, a) + line.slice(b + 1);
    } else {
      const s = Math.min(startLine, endLine);
      const e = Math.max(startLine, endLine);
      const firstLine = lines[s] ?? "";
      const lastLine = lines[e] ?? "";
      const leftCol = startLine < endLine ? startCol : endCol;
      const rightCol = startLine < endLine ? endCol : startCol;
      lines[s] = firstLine.slice(0, leftCol) + (rightCol >= 0 ? lastLine.slice(rightCol + 1) : lastLine);
      lines.splice(s + 1, e - s);
    }
    this.setText(lines.join("\n"));
    const target = Math.min(startLine, lines.length - 1);
    this.goToLineAbs(target);
    this.motionHome();
    this.motionRight(Math.max(0, startCol));
  }

  // ───────────────────────────────────────────────────────────
  // Join
  // ───────────────────────────────────────────────────────────

  private joinLines(count: number) {
    for (let i = 0; i < count - 1; i++) {
      const curLine = this.getCursorLine0();
      const lines = this.getLines();
      if (curLine >= lines.length - 1) break;
      this.motionEnd();
      const currentContent = lines[curLine] ?? "";
      if (currentContent.trimEnd().length > 0) {
        super.handleInput(" ");
        this.deleteToEnd();
      } else {
        this.deleteToEnd();
      }
    }
    this.syncState();
    this.tuiRef.requestRender();
  }

  // ───────────────────────────────────────────────────────────
  // Yank helpers
  // ───────────────────────────────────────────────────────────

  private yankLines(start: number, end: number) {
    const text = this.getText();
    const lines = text.split("\n");
    const s = Math.min(start, end);
    const e = Math.max(start, end);
    const yanked = lines.slice(s, e + 1).join("\n");
    this.yankBuffer = yanked + "\n";
    this.yankType = "line";
  }

  private yankCharRange(startLine: number, startCol: number, endLine: number, endCol: number) {
    const text = this.getText();
    const lines = text.split("\n");
    if (startLine === endLine) {
      const line = lines[startLine] ?? "";
      const a = Math.min(startCol, endCol);
      const b = Math.min(Math.max(startCol, endCol) + 1, line.length);
      if (b > a) this.yankBuffer = line.slice(a, b);
      else this.yankBuffer = "";
    } else {
      const s = Math.min(startLine, endLine);
      const e = Math.max(startLine, endLine);
      const firstLine = lines[s] ?? "";
      const lastLine = lines[e] ?? "";
      const leftCol = startLine < endLine ? startCol : endCol;
      const rightCol = startLine < endLine ? endCol : startCol;
      const parts: string[] = [firstLine.slice(leftCol)];
      for (let l = s + 1; l < e; l++) parts.push(lines[l] ?? "");
      if (rightCol >= 0) parts.push(lastLine.slice(0, rightCol + 1));
      this.yankBuffer = parts.join("\n");
    }
    this.yankType = "char";
  }

  // ───────────────────────────────────────────────────────────
  // Put helpers
  // ───────────────────────────────────────────────────────────

  private putAfterCursor() {
    if (!this.yankBuffer) return;
    if (this.yankType === "line") {
      const text = this.getText();
      const lines = text.split("\n");
      const cur = this.getCursorLine0();
      const putLines = this.yankBuffer.split("\n");
      if (putLines.length > 0 && putLines[putLines.length - 1] === "") putLines.pop();
      lines.splice(cur + 1, 0, ...putLines);
      this.setText(lines.join("\n"));
      this.goToLineAbs(cur + 1);
      this.motionFirstNonBlank();
    } else {
      const text = this.getText();
      const lines = text.split("\n");
      const curLine = this.getCursorLine0();
      const curCol = this.getCursorCol0();
      const line = lines[curLine] ?? "";
      const putText = this.yankBuffer;
      const hasNewline = putText.includes("\n");
      if (hasNewline) {
        const putLines = putText.split("\n");
        const after = line.slice(curCol + 1);
        lines[curLine] = line.slice(0, curCol + 1) + putLines[0];
        for (let i = 1; i < putLines.length - 1; i++) {
          lines.splice(curLine + i, 0, putLines[i]);
        }
        const lastPutLine = putLines[putLines.length - 1];
        lines.splice(curLine + putLines.length - 1, 0, lastPutLine + after);
        this.setText(lines.join("\n"));
        this.goToLineAbs(curLine + putLines.length - 1);
        this.motionHome();
        this.motionRight(lastPutLine.length);
      } else {
        const insertPos = Math.min(curCol + 1, line.length);
        lines[curLine] = line.slice(0, insertPos) + putText + line.slice(insertPos);
        this.setText(lines.join("\n"));
        this.goToLineAbs(curLine);
        this.motionHome();
        this.motionRight(insertPos + putText.length - 1);
      }
    }
    this.clampNormalCursor();
  }

  private putBeforeCursor() {
    if (!this.yankBuffer) return;
    if (this.yankType === "line") {
      const text = this.getText();
      const lines = text.split("\n");
      const cur = this.getCursorLine0();
      const putLines = this.yankBuffer.split("\n");
      if (putLines.length > 0 && putLines[putLines.length - 1] === "") putLines.pop();
      lines.splice(cur, 0, ...putLines);
      this.setText(lines.join("\n"));
      this.goToLineAbs(cur);
      this.motionFirstNonBlank();
    } else {
      const text = this.getText();
      const lines = text.split("\n");
      const curLine = this.getCursorLine0();
      const curCol = this.getCursorCol0();
      const line = lines[curLine] ?? "";
      const putText = this.yankBuffer;
      const hasNewline = putText.includes("\n");
      if (hasNewline) {
        const putLines = putText.split("\n");
        const after = line.slice(curCol);
        lines[curLine] = line.slice(0, curCol) + putLines[0];
        for (let i = 1; i < putLines.length - 1; i++) {
          lines.splice(curLine + i, 0, putLines[i]);
        }
        const lastPutLine = putLines[putLines.length - 1];
        lines.splice(curLine + putLines.length - 1, 0, lastPutLine + after);
        this.setText(lines.join("\n"));
        this.goToLineAbs(curLine + putLines.length - 1);
        this.motionHome();
        this.motionRight(lastPutLine.length);
      } else {
        const insertPos = Math.min(curCol, line.length);
        lines[curLine] = line.slice(0, insertPos) + putText + line.slice(insertPos);
        this.setText(lines.join("\n"));
        this.goToLineAbs(curLine);
        this.motionHome();
        this.motionRight(insertPos + putText.length - 1);
      }
    }
    this.clampNormalCursor();
  }

  // ───────────────────────────────────────────────────────────
  // Execute operator on a contiguous range of lines
  // ───────────────────────────────────────────────────────────

  private execLineOpRange(op: Operator, start: number, end: number) {
    this.saveUndoState();
    const s = Math.min(start, end);
    const e = Math.max(start, end);
    const cur = this.getCursorLine0();

    if (op === "y") {
      this.yankLines(s, e);
      this.goToLineAbs(cur);
      this.motionFirstNonBlank();
      this.recordLastChange("lineOp", op, 1, { startLineOp: s, endLineOp: e });
    } else if (op === "d") {
      this.deleteLineRange(s, e);
      this.recordLastChange("lineOp", op, 1, { startLineOp: s, endLineOp: e });
    } else if (op === "c") {
      this.deleteLineRange(s, e);
      this.recordLastChange("lineOp", op, 1, { startLineOp: s, endLineOp: e });
      this.mode = "INSERT";
    } else if (op === ">" || op === "<") {
      if (op === ">") {
        for (let l = s; l <= e; l++) {
          this.goToLineAbs(l);
          this.motionHome();
          super.handleInput("    ");
        }
      } else {
        for (let l = s; l <= e; l++) {
          this.goToLineAbs(l);
          this.motionHome();
          const line = this.lineAt(l);
          const indent = line.length - line.trimStart().length;
          const toRemove = Math.min(4, indent);
          for (let i = 0; i < toRemove; i++) this.deleteCharRightChars(1);
        }
      }
      this.goToLineAbs(cur);
      this.motionFirstNonBlank();
      this.recordLastChange("lineOp", op, 1, { startLineOp: s, endLineOp: e });
    }

    this.pendingOp = null;
    this.syncState();
    this.tuiRef.requestRender();
  }

  // ───────────────────────────────────────────────────────────
  // Execute operator with a motion (character-wise)
  // ───────────────────────────────────────────────────────────

  private execOpOnRange(op: Operator, startLine: number, startCol: number,
                         endLine: number, endCol: number, inclusive: boolean) {
    if (op === "y") {
      if (startLine !== endLine) {
        const realEnd = inclusive ? endCol : endCol - 1;
        this.yankCharRange(startLine, startCol, endLine, realEnd);
      } else {
        const a = Math.min(startCol, endCol);
        const b = inclusive ? Math.max(startCol, endCol) : Math.max(startCol, endCol) - 1;
        if (b >= a) this.yankCharRange(startLine, a, endLine, b);
      }
      this.goToLineAbs(startLine);
      this.motionHome();
      this.motionRight(startCol);
      this.clampNormalCursor();
      this.recordLastChange("charRange", op, 1, {
        startLine, startCol, endLine, endCol, inclusive,
      });
      this.pendingOp = null;
      this.syncState();
      this.tuiRef.requestRender();
      return;
    }

    if (op === ">" || op === "<") {
      this.execLineOpRange(op, startLine, endLine);
      return;
    }

    // d or c
    this.saveUndoState();

    if (startLine !== endLine) {
      const realEndCol = inclusive ? endCol : endCol - 1;
      this.deleteCrossLineRange(startLine, startCol, endLine, realEndCol);
      this.recordLastChange("charRange", op, 1, {
        startLine, startCol, endLine, endCol, inclusive,
      });
      if (op === "c") this.mode = "INSERT";
    } else {
      const lineLen = this.lineAt(startLine).length;
      const a = Math.min(startCol, endCol);
      const bExcl = inclusive ? Math.max(startCol, endCol) : Math.max(startCol, endCol) - 1;
      const b = Math.min(bExcl, lineLen - 1);
      if (b < a || a >= lineLen) {
        this.goToLineAbs(startLine);
        this.motionHome();
        this.motionRight(Math.min(startCol, lineLen > 0 ? lineLen - 1 : 0));
        this.pendingOp = null;
        this.syncState();
        this.tuiRef.requestRender();
        return;
      }
      this.goToLineAbs(startLine);
      this.motionHome();
      this.motionRight(a);
      const delCount = b - a + 1;
      for (let i = 0; i < delCount; i++) this.deleteCharRightChars(1);
      this.recordLastChange("charRange", op, 1, {
        startLine: startLine, startCol: a, endLine: startLine, endCol: b, inclusive: true,
      });
      if (op === "c") this.mode = "INSERT";
    }

    this.pendingOp = null;
    this.syncState();
    this.tuiRef.requestRender();
  }

  // ───────────────────────────────────────────────────────────
  // Last change recording (for '.' repeat)
  // ───────────────────────────────────────────────────────────

  private recordLastChange(type: LastChange["type"], op: Operator, count: number,
                            extra?: Partial<LastChange>) {
    this.lastChange = { type, op, count, ...extra };
  }

  private repeatLastChange() {
    if (!this.lastChange) return;
    const lc = this.lastChange;
    this.pendingOp = lc.op;

    if (lc.type === "lineOp" && lc.startLineOp !== undefined && lc.endLineOp !== undefined) {
      const cur = this.getCursorLine0();
      const s = lc.startLineOp;
      const e = lc.endLineOp;
      const range = e - s;
      // Apply relative to current cursor
      this.execLineOpRange(lc.op, cur, Math.min(cur + range, this.lineCount() - 1));
    } else if (lc.type === "charRange" && lc.startLine !== undefined) {
      // Best-effort: use the motion again
      const startLine = this.getCursorLine0();
      const startCol = this.getCursorCol0();
      // We can't perfectly replay a specific char range; approximate with motion
      // For simplicity, re-execute using the same rel positions
      if (lc.op === "c") {
        this.saveUndoState();
        this.deleteToEnd();
        this.mode = "INSERT";
      } else if (lc.op === "d") {
        this.saveUndoState();
        this.deleteToEnd();
      } else if (lc.op === "y") {
        const curLine = this.getCursorLine0();
        const curCol = this.getCursorCol0();
        const line = this.lineAt(curLine);
        this.yankBuffer = line.slice(curCol);
        this.yankType = "char";
      }
      this.pendingOp = null;
    } else if (lc.type === "visual") {
      // Replay visual operation
      this._visualType = lc.visualType || "char";
      this.visualStartLine = this.getCursorLine0();
      this.visualStartCol = this.getCursorCol0();
      this.mode = "VISUAL";
      // Can't perfectly replay; just enter visual at cursor
    } else if (lc.type === "simple") {
      // Simple operations (C, s, x, etc.)
      if (lc.op === "c") {
        // C or s: delete and enter insert mode
        this.saveUndoState();
        if (lc.count > 1) {
          // s with count: delete count chars
          this.deleteCharRightChars(Math.min(lc.count, Math.max(0, this.lineAt(this.getCursorLine0()).length - this.getCursorCol0())));
        } else {
          // C: delete to end of line
          this.deleteToEnd();
        }
        this.mode = "INSERT";
      } else if (lc.op === "d") {
        // D: delete to end of line
        this.saveUndoState();
        this.deleteToEnd();
      } else {
        this.execLineOpRange(lc.op, this.getCursorLine0(), this.getCursorLine0());
      }
    } else {
      // Fallback: repeat op at current position
      this.execLineOpRange(lc.op, this.getCursorLine0(), this.getCursorLine0());
    }
    this.syncState();
    this.tuiRef.requestRender();
  }

  // ───────────────────────────────────────────────────────────
  // Text objects: find ranges for iw, aw, i(, a(, i", a", etc.
  // ───────────────────────────────────────────────────────────

  /** Find the range of an inner word (iw). Returns {line, startCol, endCol}. */
  private findInnerWord(): { sLine: number; sCol: number; eLine: number; eCol: number } | null {
    const lines = this.getLines();
    let line = this.getCursorLine0();
    let col = this.getCursorCol0();
    const curLine = lines[line] ?? "";

    if (col >= curLine.length) col = Math.max(0, curLine.length - 1);
    const isWord = VimEditor.isWordChar;

    // If on whitespace, do nothing (or find nearest word)
    if (!isWord(curLine[col] ?? "")) return null;

    // Find start of word
    let sCol = col;
    while (sCol > 0 && isWord(curLine[sCol - 1] ?? "")) sCol--;

    // Find end of word
    let eCol = col;
    while (eCol < curLine.length && isWord(curLine[eCol])) eCol++;
    eCol = Math.max(sCol, eCol - 1); // inclusive

    return { sLine: line, sCol, eLine: line, eCol };
  }

  /** Find the range of a word including surrounding whitespace (aw). */
  private findAWord(): { sLine: number; sCol: number; eLine: number; eCol: number } | null {
    const inner = this.findInnerWord();
    if (!inner) return null;
    const lines = this.getLines();
    const curLine = lines[inner.sLine] ?? "";
    const isWord = VimEditor.isWordChar;
    const isSpace = (ch: string) => ch === " " || ch === "\t";

    // Include trailing whitespace
    let eCol = inner.eCol + 1;
    while (eCol < curLine.length && isSpace(curLine[eCol])) eCol++;
    eCol = Math.max(inner.eCol, eCol - 1);

    // If no trailing whitespace, try leading
    if (eCol === inner.eCol) {
      let sCol = inner.sCol - 1;
      while (sCol >= 0 && isSpace(curLine[sCol])) sCol--;
      return { sLine: inner.sLine, sCol: sCol + 1, eLine: inner.eLine, eCol };
    }

    return { sLine: inner.sLine, sCol: inner.sCol, eLine: inner.eLine, eCol };
  }

  /**
   * Find block range for i( / a( / i{ / a{ / i[ / a[ / i< / a<
   * `include` = true for a(, false for i(
   * `open` is the opening char, `close` is the matching closing char.
   */
  private findBlockRange(open: string, close: string, include: boolean):
    { sLine: number; sCol: number; eLine: number; eCol: number } | null {
    const lines = this.getLines();
    let line = this.getCursorLine0();
    let col = this.getCursorCol0();
    const maxLine = lines.length - 1;

    // If we're on the opening bracket, search forward to closing.
    const curCh = (lines[line] ?? "")[col] ?? "";
    if (curCh === open) {
      let depth = 1;
      let fl = line, fc = col + 1;
      while (fl <= maxLine) {
        const ln = lines[fl] ?? "";
        while (fc < ln.length) {
          if (ln[fc] === open) depth++;
          else if (ln[fc] === close) { depth--; if (depth === 0) break; }
          fc++;
        }
        if (depth === 0) break;
        fl++; fc = 0;
      }
      if (depth !== 0) return null;
      if (include) return { sLine: line, sCol: col, eLine: fl, eCol: fc };
      const eColAdj = fc > 0 ? fc - 1 : fc;
      const sColAdj = col + 1;
      if (sColAdj > eColAdj && line === fl) return null;
      return { sLine: line, sCol: sColAdj, eLine: fl, eCol: eColAdj };
    }

    // If we're on the closing bracket, search backward to opening.
    if (curCh === close) {
      let depth = 1;
      let bl = line, bc = col - 1;
      while (bl >= 0) {
        const ln = lines[bl] ?? "";
        while (bc >= 0) {
          if (ln[bc] === close) depth++;
          else if (ln[bc] === open) { depth--; if (depth === 0) break; }
          bc--;
        }
        if (depth === 0) break;
        bl--; bc = bl >= 0 ? (lines[bl] ?? "").length - 1 : -1;
      }
      if (depth !== 0) return null;
      if (include) return { sLine: bl, sCol: bc, eLine: line, eCol: col };
      const sColAdj = bc + 1;
      const eColAdj = col > 0 ? col - 1 : col;
      if (sColAdj > eColAdj && bl === line) return null;
      return { sLine: bl, sCol: sColAdj, eLine: line, eCol: eColAdj };
    }

    // Cursor is not on a bracket: try backward search, then forward.
    // Neovim's current_block: first findmatch(NULL, what) backward,
    // then findmatchlimit(NULL, what, FM_FORWARD, 0) forward.
    let startLine = -1, startCol = -1;
    let depth = 0;

    // First: search backward from cursor for an unclosed opening bracket.
    let bl = line, bc = col;
    while (bl >= 0) {
      const ln = lines[bl] ?? "";
      while (bc >= 0) {
        const c = ln[bc] ?? "";
        if (c === close) depth++;
        else if (c === open) {
          if (depth === 0) { startLine = bl; startCol = bc; break; }
          depth--;
        }
        bc--;
      }
      if (startLine >= 0) break;
      bl--; bc = bl >= 0 ? (lines[bl] ?? "").length - 1 : -1;
    }

    // If backward search failed, try forward: find a closing bracket and
    // then search backward for its opening.
    if (startLine < 0) {
      let fl = line, fc = col;
      depth = 0;
      while (fl <= maxLine) {
        const ln = lines[fl] ?? "";
        while (fc < ln.length) {
          const c = ln[fc];
          if (c === open) depth++;
          else if (c === close) {
            if (depth === 0) {
              // Found unclosed closing bracket; search backward for opening.
              let bbl = fl, bbc = fc - 1;
              let bdepth = 0;
              while (bbl >= 0) {
                const bln = lines[bbl] ?? "";
                while (bbc >= 0) {
                  const bc2 = bln[bbc] ?? "";
                  if (bc2 === close) bdepth++;
                  else if (bc2 === open) {
                    if (bdepth === 0) { startLine = bbl; startCol = bbc; break; }
                    bdepth--;
                  }
                  bbc--;
                }
                if (startLine >= 0) break;
                bbl--; bbc = bbl >= 0 ? (lines[bbl] ?? "").length - 1 : -1;
              }
              break;
            }
            depth--;
          }
          fc++;
        }
        if (startLine >= 0) break;
        fl++; fc = 0;
      }
    }

    if (startLine < 0) return null; // No bracket found

    // Search forward from opening for matching closing
    let fl = startLine, fc = startCol + 1;
    depth = 0;
    while (fl <= maxLine) {
      const ln = lines[fl] ?? "";
      while (fc < ln.length) {
        if (ln[fc] === open) depth++;
        else if (ln[fc] === close) { if (depth === 0) break; depth--; }
        fc++;
      }
      if (depth === 0 && fc < ln.length && ln[fc] === close) break;
      fl++; fc = 0;
    }
    if (fl > maxLine) return null;

    if (include) return { sLine: startLine, sCol: startCol, eLine: fl, eCol: fc };
    // inner: exclude brackets
    const sColAdj = startCol + 1;
    const eColAdj = fc > 0 ? fc - 1 : fc;
    if (sColAdj > eColAdj && startLine === fl) return null;
    return { sLine: startLine, sCol: sColAdj, eLine: fl, eCol: eColAdj };
  }

  /**
   * Find quote range on the current line.
   * `include` = true for a", false for i".
   */
  private findQuoteRange(quote: string, include: boolean):
    { sLine: number; sCol: number; eLine: number; eCol: number } | null {
    const lines = this.getLines();
    const line = this.getCursorLine0();
    const curLine = lines[line] ?? "";
    const col = this.getCursorCol0();

    // Search backward for the opening quote
    let sCol = col;
    let escaped = false;
    while (sCol > 0) {
      sCol--;
      if (curLine[sCol] === "\\") { escaped = !escaped; continue; }
      if (curLine[sCol] === quote && !escaped) break;
      escaped = false;
    }
    if (curLine[sCol] !== quote) {
      // No opening before cursor; search forward for first quote
      sCol = col;
      while (sCol < curLine.length && curLine[sCol] !== quote) sCol++;
      if (sCol >= curLine.length) return null;
    }

    // Search forward for closing quote
    let eCol = sCol + 1;
    escaped = false;
    while (eCol < curLine.length) {
      if (curLine[eCol] === "\\") { escaped = !escaped; eCol++; continue; }
      if (curLine[eCol] === quote && !escaped) break;
      escaped = false;
      eCol++;
    }
    if (eCol >= curLine.length || curLine[eCol] !== quote) return null;

    if (include) return { sLine: line, sCol, eLine: line, eCol };
    // inner: exclude quotes
    if (sCol + 1 > eCol - 1) return null;
    return { sLine: line, sCol: sCol + 1, eLine: line, eCol: eCol - 1 };
  }

  /** Apply an operator to a text object range. */
  private applyOpToTextObj(op: Operator, trange: { sLine: number; sCol: number; eLine: number; eCol: number }) {
    // Move cursor to end of range
    this.gotoAbs(trange.eLine, trange.eCol);
    // The range is inclusive on both ends
    this.execOpOnRange(op, trange.sLine, trange.sCol, trange.eLine, trange.eCol, true);
  }

  // ───────────────────────────────────────────────────────────
  // Search
  // ───────────────────────────────────────────────────────────

  /** Enter search mode with given direction prefix. */


  /** Execute a search for the given pattern. */
  private doSearch(pattern: string, dir: "/" | "?") {
    if (!pattern) return;
    this.lastSearchPattern = pattern;
    this.lastSearchDir = dir;

    const lines = this.getLines();
    const curLine = this.getCursorLine0();
    const curCol = this.getCursorCol0();
    const forward = dir === "/";

    // Neovim: search wraps around.
    // Start searching on the current line from the next/prev character.
    const step = forward ? 1 : -1;
    let startCol = forward ? curCol + 1 : curCol - 1;

    // First pass: search from cursor position to end/beginning of buffer.
    for (let l = curLine; forward ? l < lines.length : l >= 0; l += step) {
      const lineText = lines[l] ?? "";
      const searchFrom = (l === curLine) ? (forward ? Math.max(0, startCol) : Math.min(startCol, lineText.length - 1)) : (forward ? 0 : lineText.length - 1);
      const idx = forward
        ? lineText.indexOf(pattern, searchFrom)
        : (searchFrom >= 0 ? lineText.lastIndexOf(pattern, searchFrom) : -1);
      if (idx !== -1) {
        this.gotoAbs(l, idx);
        this.syncState();
        this.tuiRef.requestRender();
        return;
      }
    }

    // Wrap around: search from beginning/end to cursor position.
    const wrapEnd = forward ? curLine : curLine;
    for (let l = forward ? 0 : lines.length - 1; forward ? l <= wrapEnd : l >= wrapEnd; l += step) {
      const lineText = lines[l] ?? "";
      const idx = forward
        ? lineText.indexOf(pattern, 0)
        : lineText.lastIndexOf(pattern, lineText.length - 1);
      if (idx !== -1) {
        // On the cursor line, make sure we don't land on the same match or past it.
        if (l === curLine) {
          const valid = forward ? idx < curCol : idx > curCol;
          if (!valid) continue;
        }
        this.gotoAbs(l, idx);
        this.syncState();
        this.tuiRef.requestRender();
        return;
      }
    }
    // Not found
    this.syncState();
    this.tuiRef.requestRender();
  }

  /** Repeat last search forward (n) or backward (N). */
  private repeatSearch(reverse: boolean) {
    if (!this.lastSearchPattern) return;
    const dir = reverse
      ? (this.lastSearchDir === "/" ? "?" as const : "/" as const)
      : this.lastSearchDir;
    this.doSearch(this.lastSearchPattern, dir);
  }

  /** Search for word under cursor (* = forward, # = backward). */
  private searchWordUnderCursor(dir: "/" | "?") {
    const lines = this.getLines();
    const line = this.getCursorLine0();
    const col = this.getCursorCol0();
    const curLine = lines[line] ?? "";
    if (col >= curLine.length) return;

    const isWord = VimEditor.isWordChar;
    if (!isWord(curLine[col])) return;

    // Find word boundaries
    let s = col, e = col;
    while (s > 0 && isWord(curLine[s - 1])) s--;
    while (e < curLine.length && isWord(curLine[e])) e++;

    const word = curLine.slice(s, e);
    if (!word) return;

    // Neovim: surround with \< and \> for whole-word search
    // We'll do simple exact match for now
    this.lastSearchPattern = word;
    this.lastSearchDir = dir;
    this.doSearch(word, dir);
  }

  // ───────────────────────────────────────────────────────────
  // Substitute command: :s/pattern/replacement/flags
  // ───────────────────────────────────────────────────────────

  private doSubstitute(cmd: string) {
    // Parse: :s/pattern/replacement/flags or :%s/...
    // Also handle :s/pattern/replacement/ and :s/pattern/replacement
    let range = "";
    let rest = cmd;

    if (rest.startsWith("%")) {
      range = "%";
      rest = rest.slice(1);
    }
    if (!rest.startsWith("s")) return;
    rest = rest.slice(1); // skip 's'

    // Find delimiter (usually / but can be other chars)
    const delim = rest[0];
    if (!delim) return;
    rest = rest.slice(1);

    // Parse pattern
    let patternEnd = -1;
    for (let i = 0; i < rest.length; i++) {
      if (rest[i] === "\\" && i + 1 < rest.length) { i++; continue; }
      if (rest[i] === delim) { patternEnd = i; break; }
    }
    if (patternEnd < 0) return;
    const pattern = rest.slice(0, patternEnd);
    rest = rest.slice(patternEnd + 1);

    // Parse replacement
    let replEnd = -1;
    for (let i = 0; i < rest.length; i++) {
      if (rest[i] === "\\" && i + 1 < rest.length) { i++; continue; }
      if (rest[i] === delim) { replEnd = i; break; }
    }
    const replacement = replEnd >= 0 ? rest.slice(0, replEnd) : rest;
    const flags = replEnd >= 0 ? rest.slice(replEnd + 1) : "";

    const global = flags.includes("g");
    const confirm = flags.includes("c");

    const text = this.getText();
    const lines = text.split("\n");

    if (confirm) return; // Skip confirm mode for now

    const appliesToAllLines = range === "%";

    if (appliesToAllLines) {
      for (let i = 0; i < lines.length; i++) {
        if (global) {
          lines[i] = lines[i].split(pattern).join(replacement);
        } else {
          lines[i] = lines[i].replace(pattern, replacement);
        }
      }
    } else {
      // Only current line
      const cur = this.getCursorLine0();
      if (global) {
        lines[cur] = lines[cur].split(pattern).join(replacement);
      } else {
        lines[cur] = lines[cur].replace(pattern, replacement);
      }
    }

    this.saveUndoState();
    this.setText(lines.join("\n"));
    this.clampNormalCursor();
    this.syncState();
    this.tuiRef.requestRender();
  }

  // ───────────────────────────────────────────────────────────
  // Main input handler
  // ───────────────────────────────────────────────────────────

  override handleInput(data: string): void {
    this.recordKey(data);

  

    // ── COMMAND mode ──
    if (this._mode === "COMMAND") {
      this.handleCommandInput(data);
      return;
    }

    // ── Escape (any mode) → NORMAL ──
    if (matchesKey(data, "escape")) {
      this.mode = "NORMAL";
      return;
    }

    // ── INSERT mode: passthrough ──
    if (this._mode === "INSERT") {
      super.handleInput(data);
      this.syncState();
      return;
    }

    // ── Pending leader (g*, z*, f/F/t/T, text objects, r, q, @, ") ──
    if (this.pendingLeader !== null) {
      this.handlePendingLeader(data);
      return;
    }

    // ── Text object modifier pending (i/a after operator) ──
    if (this.textObjMod !== null) {
      this.handleTextObject(data);
      return;
    }

    // ── VISUAL mode ──
    if (this._mode === "VISUAL") {
      this.handleVisualInput(data);
      return;
    }

    // ── NORMAL mode: forward unrecognized keys to Pi ──
    if (!this.handleNormalInput(data)) {
      super.handleInput(data);
    }
  }

  // ───────────────────────────────────────────────────────────
  // NORMAL mode input
  // ───────────────────────────────────────────────────────────

  private handleNormalInput(data: string): boolean {
    // ── Register prefix: " + letter ──
    if (data === '"') {
      this.pendingLeader = '"';
      return true;
    }

    // ── Ctrl+R redo (try both raw and Key match) ──
    if (matchesKey(data, Key.ctrl("r")) || data === "\x12") {
      this.pendingLeader = null;
      this.countBuf = "";
      const count = this.consumeCount(1);
      for (let i = 0; i < count; i++) this.redoOne();
      this.clampNormalCursor();
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── Ctrl+F page down, Ctrl+B page up ──
    if (matchesKey(data, Key.ctrl("f")) || data === "\x06") {
      const count = this.consumeCount(1);
      for (let i = 0; i < count; i++) this.pageDown();
      this.clampNormalCursor();
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }
    if (matchesKey(data, Key.ctrl("b")) || data === "\x02") {
      const count = this.consumeCount(1);
      for (let i = 0; i < count; i++) this.pageUp();
      this.clampNormalCursor();
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }
    // Ctrl+D half-page down, Ctrl+U half-page up
    if (matchesKey(data, Key.ctrl("d")) || data === "\x04") {
      const count = this.consumeCount(1);
      for (let i = 0; i < count; i++) { this.pageDown(); this.pageDown(); } // approx
      this.clampNormalCursor();
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }
    if (matchesKey(data, Key.ctrl("u")) || data === "\x15") {
      const count = this.consumeCount(1);
      for (let i = 0; i < count; i++) { this.pageUp(); this.pageUp(); }
      this.clampNormalCursor();
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── Digit: accumulate count ──
    if (this.isDigit(data)) {
      if (data === "0" && this.countBuf === "" && this.pendingOp === null && this.pendingLeader === null) {
        this.motionFirstNonBlank();
        this.syncState();
        this.tuiRef.requestRender();
        return true;
      }
      this.countBuf += data;
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── Multi-key leaders: g, z, f, F, t, T ──
    if (data === "g" || data === "z" || data === "f" || data === "F" || data === "t" || data === "T") {
      this.pendingLeader = data;
      return true;
    }

    // ── Operators: d, c, y, >, < ──
    if (data === "d" || data === "c" || data === "y" || data === ">" || data === "<") {
      this.handleOperator(data);
      return true;
    }

    // ── : enters COMMAND mode ──
    if (data === ":") {
      this._mode = "COMMAND";
      this.commandBuffer = ":";
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── Normal commands ──
    return this.handleNormalCmd(data);
  }

  /** Handle operator key press (d, c, y, >, <). */
  private handleOperator(opChar: string) {
    const op = opChar as Operator;

    if (this.pendingOp === op) {
      // Double-tap = linewise operator (dd, cc, yy, >>, <<)
      const count = this.consumeCount(1);
      const cur = this.getCursorLine0();
      const end = Math.min(cur + count - 1, this.lineCount() - 1);
      this.execLineOpRange(op, cur, end);
    } else {
      this.pendingOp = op;
      this.syncState();
      this.tuiRef.requestRender();
    }
  }

  /** Handle a normal-mode command key. */
  private handleNormalCmd(data: string): boolean {
    const op = this.pendingOp;

    // ── n/N: repeat search ──
    if (data === "n" || data === "N") {
      const count = this.consumeCount(1);
      for (let i = 0; i < count; i++) this.repeatSearch(data === "N");
      this.pendingOp = null;
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── * / #: search word under cursor ──
    if (data === "*" || data === "#") {
      this.pendingOp = null;
      this.searchWordUnderCursor(data === "*" ? "/" : "?");
      return true;
    }

    // ── . repeat last change ──
    if (data === ".") {
      const count = this.consumeCount(1);
      for (let i = 0; i < count; i++) this.repeatLastChange();
      this.pendingOp = null;
      return;
    }

    // ── C: change to end of line (c$) ──
    if (data === "C") {
      const startLineC = this.getCursorLine0();
      const startColC = this.getCursorCol0();
      if (op) {
        // Operator pending: C acts as $ motion
        this.motionDollar();
        const endLineC = this.getCursorLine0();
        const endColC = this.getCursorCol0();
        this.execOpOnRange(op, startLineC, startColC, endLineC, endColC, true);
      } else {
        this.saveUndoState();
        this.deleteToEnd();
        this.recordLastChange("simple", "c", 1);
        this.pendingOp = null;
        // After deleteToEnd, the cursor is at the deletion start position.
        // Don't clamp - we want INSERT mode to start exactly here (Neovim: c$).
        this.mode = "INSERT";
      }
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── s: substitute char (cl) ──
    if (data === "s") {
      const count = this.consumeCount(1);
      this.saveUndoState();
      this.deleteCharRightChars(Math.min(count, Math.max(0, this.lineAt(this.getCursorLine0()).length - this.getCursorCol0())));
      this.recordLastChange("simple", "c", count);
      this.pendingOp = null;
      this.mode = "INSERT";
      return true;
    }

    // ── S: substitute line (cc) ──
    if (data === "S") {
      const count = this.consumeCount(1);
      const cur = this.getCursorLine0();
      const end = Math.min(cur + count - 1, this.lineCount() - 1);
      this.execLineOpRange("c", cur, end);
      return true;
    }

    // ── Y: linewise yank (Neovim: Y → yy) ──
    if (data === "Y") {
      const count = this.consumeCount(1);
      const cur = this.getCursorLine0();
      const end = Math.min(cur + count - 1, this.lineCount() - 1);
      this.yankLines(cur, end);
      this.goToLineAbs(cur);
      this.motionFirstNonBlank();
      this.recordLastChange("lineOp", "y", count, { startLineOp: cur, endLineOp: end });
      this.pendingOp = null;
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── D: delete to end of line ──
    if (data === "D") {
      const startLineD = this.getCursorLine0();
      const startColD = this.getCursorCol0();
      if (op) {
        this.motionDollar();
        const endLineD = this.getCursorLine0();
        const endColD = this.getCursorCol0();
        this.execOpOnRange(op, startLineD, startColD, endLineD, endColD, true);
      } else {
        this.saveUndoState();
        this.deleteToEnd();
        this.recordLastChange("simple", "d", 1);
        this.clampNormalCursor();
        this.pendingOp = null;
      }
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── { / }: paragraph motions ──
    if (data === "{" || data === "}") {
      const startLineP = this.getCursorLine0();
      const startColP = this.getCursorCol0();
      const count = this.consumeCount(1);
      const hasOp = op !== null;

      if (data === "{") this.motionPrevParagraph(count);
      else this.motionNextParagraph(count);

      if (!op) this.clampNormalCursor();
      if (op) {
        const endLine = this.getCursorLine0();
        // Paragraph motions are linewise
        this.execLineOpRange(op, startLineP, endLine);
      }
      this.pendingOp = null;
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── %: bracket matching ──
    if (data === "%") {
      const startLinePct = this.getCursorLine0();
      const startColPct = this.getCursorCol0();
      this.motionPercent();
      if (!op) this.clampNormalCursor();
      if (op) {
        const endLine = this.getCursorLine0();
        const endCol = this.getCursorCol0();
        this.execOpOnRange(op, startLinePct, startColPct, endLine, endCol, true);
      }
      this.pendingOp = null;
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── H / M / L: screen jumps ──
    if (data === "H" || data === "M" || data === "L") {
      const startLineS = this.getCursorLine0();
      const startColS = this.getCursorCol0();
      const count = this.consumeCount(1);

      if (data === "H") this.motionScreenTop(count);
      else if (data === "M") this.motionScreenMiddle();
      else this.motionScreenBottom(count);

      if (!op) this.clampNormalCursor();
      if (op) {
        const endLine = this.getCursorLine0();
        this.execLineOpRange(op, startLineS, endLine);
      }
      this.pendingOp = null;
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── Text object: i/a ──
    if (data === "i" || data === "a") {
      if (op) {
        // Operator pending: i/a become text object selectors
        this.textObjMod = data as "i" | "a";
        this.syncState();
        this.tuiRef.requestRender();
        return true;
      }
      // No operator: fall through to insert mode handlers
    }

    // ── First, try non-motion commands ──
    if (this.handleNonMotionCmd(data)) {
      this.pendingOp = null;
      this.syncState();
      this.tuiRef.requestRender();
      return true;
    }

    // ── Motions ──
    const startLine = this.getCursorLine0();
    const startCol = this.getCursorCol0();
    const count = this.consumeCount(1);
    const hasOp = op !== null;

    // cw/cW special case → ce/cE when cursor is on a word char
    let motionData = data;
    let motionInclusive = false;
    if (op === "c" && (data === "w" || data === "W") && !this.cursorLineEmpty()) {
      const curLine = this.lineAt(this.getCursorLine0());
      const curCol = this.getCursorCol0();
      const ch = curCol < curLine.length ? curLine[curCol] : "";
      const isW = data === "W" ? VimEditor.isNonBlank : VimEditor.isWordChar;
      if (ch && isW(ch)) {
        motionData = data === "w" ? "e" : "E";
        motionInclusive = true;
      }
    }

    const motionResult = this.applyNormalMotion(motionData, count, hasOp);
    if (motionResult !== null) {
      if (!op) this.clampNormalCursor();
      if (op) {
        const endLine = this.getCursorLine0();
        const endCol = this.getCursorCol0();
        const inclusive = motionResult || motionInclusive;
        this.execOpOnRange(op, startLine, startCol, endLine, endCol, inclusive);
      }
    }

    this.pendingOp = null;
    this.syncState();
    this.tuiRef.requestRender();
    return motionResult !== null;
  }

  /** Non-motion commands. Returns true if handled. */
  private handleNonMotionCmd(data: string): boolean {
    // Don't consume count for leader commands (r, q, @): they keep it in countBuf
    const leaderCmds = ["r", "q", "@"];
    const count = leaderCmds.includes(data) ? 1 : this.consumeCount(1);

    switch (data) {
      case "u":
        for (let i = 0; i < count; i++) this.undoOne();
        this.clampNormalCursor();
        return true;

      case "J":
        this.saveUndoState();
        this.joinLines(count > 1 ? count : 2);
        return true;

      case "K":
        // No-op: unrecognised command
        return true;

      case "p":
        this.saveUndoState();
        for (let i = 0; i < count; i++) this.putAfterCursor();
        return true;

      case "P":
        this.saveUndoState();
        for (let i = 0; i < count; i++) this.putBeforeCursor();
        return true;

      case "r":
        this.pendingLeader = "r";
        // count stays in countBuf for handlePendingLeader to use
        return true;

      case "q":
        this.pendingLeader = "q";
        return true;

      case "@":
        this.pendingLeader = "@";
        return true;

      case "v":
        this._visualType = "char";
        this.mode = "VISUAL";
        return true;

      case "V":
        this._visualType = "line";
        this.mode = "VISUAL";
        return true;

      case "i":
        this.saveUndoState();
        this.mode = "INSERT";
        return true;

      case "I":
        this.saveUndoState();
        this.motionFirstNonBlank();
        this.mode = "INSERT";
        return true;

      case "a":
        this.saveUndoState();
        this.motionRight(1);
        this.mode = "INSERT";
        return true;

      case "A":
        this.saveUndoState();
        this.motionEnd();
        this.mode = "INSERT";
        return true;

      case "o":
        this.saveUndoState();
        {
          const tx = this.getText();
          const ls = tx.split("\n");
          const cur = this.getCursorLine0();
          ls.splice(cur + 1, 0, "");
          this.setText(ls.join("\n"));
          this.goToLineAbs(cur + 1);
          this.motionHome();
          this.mode = "INSERT";
        }
        return true;

      case "O":
        this.saveUndoState();
        {
          const tx = this.getText();
          const ls = tx.split("\n");
          const cur = this.getCursorLine0();
          ls.splice(cur, 0, "");
          this.setText(ls.join("\n"));
          this.goToLineAbs(cur);
          this.motionHome();
          this.mode = "INSERT";
        }
        return true;

      case "x":
        this.saveUndoState();
        this.deleteCharRightChars(count);
        this.clampNormalCursor();
        return true;

      case "X":
        this.saveUndoState();
        this.deleteCharLeft(count);
        return true;

      default:
        return false;
    }
  }

  /** Apply a normal-mode motion. */
  private applyNormalMotion(data: string, count: number, hasOp: boolean): boolean | null {
    switch (data) {
      case "h": this.motionLeft(count);     return false;
      case "j": this.motionDown(count);     return false;
      case "k": this.motionUp(count);       return false;
      case "l": this.motionRight(count);    return false;

      case "w": this.motionWordForward(count, false, hasOp); return false;
      case "W": this.motionWordForward(count, true, hasOp);  return false;
      case "b": this.motionWordBackward(count, false);       return false;
      case "B": this.motionWordBackward(count, true);        return false;

      case "e": this.motionWordEnd(count, false); return true;
      case "E": this.motionWordEnd(count, true);  return true;

      case "0": this.motionHome();           return false;
      case "^": this.motionFirstNonBlank();   return false;
      case "$": this.motionDollar();          return true;
      case "_":
        this.motionDown(Math.max(0, count - 1));
        this.motionFirstNonBlank();
        return false;
      case "G":
        if (count > 1) this.goToLineAbs(count - 1);
        else this.goToLineAbs(this.lineCount() - 1);
        this.motionFirstNonBlank();
        return false;

      default:
        this.pendingOp = null;
        return null;
    }
  }

  // ───────────────────────────────────────────────────────────
  // Pending leader handler (g*, z*, f/F/t/T, ", q, @, r)
  // ───────────────────────────────────────────────────────────

  private handlePendingLeader(data: string) {
    const leader = this.pendingLeader!;
    this.pendingLeader = null;

    if (leader === '"') {
      this.registerName = data;
      this.syncState();
      this.tuiRef.requestRender();
      return;
    }

    if (leader === "r") {
      // Replace character (count-aware: 3rx replaces 3 chars with x)
      const rcount = Math.max(1, Number.parseInt(this.countBuf, 10) || 1);
      this.countBuf = "";
      for (let i = 0; i < rcount; i++) this.deleteCharRightChars(1);
      if (data.length === 1 && data.charCodeAt(0) >= 32) {
        for (let i = 0; i < rcount; i++) super.handleInput(data);
      }
      this.mode = "NORMAL";
      return;
    }

    if (leader === "q") {
      if (data === "q" || data === "Q") {
        this.stopRecording();
      } else {
        this.startRecording(data);
      }
      return;
    }

    if (leader === "@") {
      this.playMacro(data);
      this.syncState();
      this.tuiRef.requestRender();
      return;
    }

    if (leader === "f" || leader === "F" || leader === "t" || leader === "T") {
      if (data.length === 1 && data.charCodeAt(0) >= 32) {
        const forward = (leader === "f" || leader === "t");
        const landBefore = (leader === "t" || leader === "T");
        const startLine = this.getCursorLine0();
        const startCol = this.getCursorCol0();
        const op = this.pendingOp;

        this.jumpToChar(data, forward, landBefore);

        // Apply pending operator if one was set
        if (op) {
          const endLine = this.getCursorLine0();
          const endCol = this.getCursorCol0();
          // f/F is inclusive of the target char, t/T is exclusive
          const inclusive = (leader === "f" || leader === "F");
          this.execOpOnRange(op, startLine, startCol, endLine, endCol, inclusive);
        }
      }
      this.syncState();
      this.tuiRef.requestRender();
      return;
    }

    if (leader === "g") {
      this.handleGCmd(data);
      return;
    }

    // "z" commands: scroll (zz, zt, zb, z., z-, etc.)
    if (leader === "z") {
      if (data === "z" || data === ".") {
        this.scrollCursorMiddle();
      } else if (data === "t" || data === "\r" || data === "\n") {
        this.scrollCursorTop();
      } else if (data === "b" || data === "-") {
        this.scrollCursorBottom();
      }
      return;
    }

    this.pendingOp = null;
    this.syncState();
    this.tuiRef.requestRender();
  }

  /** Handle g-prefixed commands. */
  private handleGCmd(data: string) {
    const op = this.pendingOp;

    if (data === "g") {
      const n = this.consumeCount(0);
      if (n > 0) this.goToLineAbs(n - 1);
      else this.goToLineAbs(0);

      if (op) {
        this.saveUndoState();
        const curLine = this.getCursorLine0();
        if (op === "d") this.deleteLineRange(0, curLine);
        else if (op === "c") { this.deleteLineRange(0, curLine); this.mode = "INSERT"; }
        else if (op === "y") this.yankLines(0, curLine);
        this.pendingOp = null;
      }
    } else if ((data === "~" || data === "u" || data === "U") && op) {
      this.pendingOp = null;
    }

    this.syncState();
    this.tuiRef.requestRender();
  }

  // ───────────────────────────────────────────────────────────
  // Text object handler (after i or a with pending operator)
  // ───────────────────────────────────────────────────────────

  private handleTextObject(data: string) {
    const mod = this.textObjMod!;
    const op = this.pendingOp;
    this.textObjMod = null;

    const include = mod === "a";
    let range: { sLine: number; sCol: number; eLine: number; eCol: number } | null = null;

    if (data === "w" || data === "W") {
      range = include ? this.findAWord() : this.findInnerWord();
    } else if (data === "(" || data === ")" || data === "b") {
      range = this.findBlockRange("(", ")", include);
    } else if (data === "{" || data === "}" || data === "B") {
      range = this.findBlockRange("{", "}", include);
    } else if (data === "[" || data === "]") {
      range = this.findBlockRange("[", "]", include);
    } else if (data === "<" || data === ">") {
      range = this.findBlockRange("<", ">", include);
    } else if (data === '"') {
      range = this.findQuoteRange('"', include);
    } else if (data === "'") {
      range = this.findQuoteRange("'", include);
    } else if (data === "`") {
      range = this.findQuoteRange("`", include);
    }

    if (!range) {
      this.pendingOp = null;
      this.syncState();
      this.tuiRef.requestRender();
      return;
    }

    // In visual mode, extend selection to the text object
    if (this._mode === "VISUAL") {
      this.visualStartLine = range.sLine;
      this.visualStartCol = range.sCol;
      this.gotoAbs(range.eLine, range.eCol);
      this.syncState();
      this.tuiRef.requestRender();
      return;
    }

    // Normal mode with operator: must have an operator pending
    if (!op) {
      this.pendingOp = null;
      this.syncState();
      this.tuiRef.requestRender();
      return;
    }

    if (range.sLine === range.eLine && range.sCol > range.eCol) {
      // Empty inner range; just drop operator
      this.pendingOp = null;
    } else {
      this.saveUndoState();
      this.applyOpToTextObj(op, range);
    }

    this.syncState();
    this.tuiRef.requestRender();
  }

  /** Forward/backward jump to character (simplified f/t/F/T). */
  private jumpToChar(ch: string, forward: boolean, landBefore: boolean) {
    const lines = this.getLines();
    let curLine = this.getCursorLine0();
    let curCol = this.getCursorCol0();
    const dir = forward ? 1 : -1;

    // Start from adjacent position (skip current character)
    curCol += dir;

    while (curLine >= 0 && curLine < lines.length) {
      const line = lines[curLine];
      while ((forward && curCol < line.length) || (!forward && curCol >= 0)) {
        if (curCol >= 0 && curCol < line.length && line[curCol] === ch) {
          this.goToLineAbs(curLine);
          this.motionHome();
          const targetCol = landBefore ? Math.max(0, curCol - 1) : curCol;
          this.motionRight(targetCol);
          return;
        }
        curCol += dir;
      }
      curLine += dir;
      if (curLine >= 0 && curLine < lines.length) {
        curCol = forward ? 0 : (lines[curLine]?.length ?? 0) - 1;
      }
    }
  }

  // ───────────────────────────────────────────────────────────
  // VISUAL mode input
  // ───────────────────────────────────────────────────────────

  private handleVisualInput(data: string) {
    // v/V toggle visual type
    if (data === "v") {
      if (this._visualType === "char") { this.mode = "NORMAL"; return; }
      this._visualType = "char";
      this.syncState(); this.tuiRef.requestRender();
      return;
    }
    if (data === "V") {
      if (this._visualType === "line") { this.mode = "NORMAL"; return; }
      this._visualType = "line";
      this.syncState(); this.tuiRef.requestRender();
      return;
    }

    // Text objects in visual mode (i/a)
    if (data === "i" || data === "a") {
      this.textObjMod = data as "i" | "a";
      this.syncState(); this.tuiRef.requestRender();
      return;
    }

    // Escape already handled

    // Operators in visual mode
    if (data === "d" || data === "x") {
      const curLine = this.getCursorLine0();
      const curCol = this.getCursorCol0();
      this.saveUndoState();
      if (this._visualType === "line") {
        this.deleteLineRange(this.visualStartLine, curLine);
        this.lastVisualStartLine = this.visualStartLine;
        this.lastVisualEndLine = curLine;
        this.lastVisualType = "line";
        this.recordLastChange("visual", "d", 1, { visualType: "line",
          visualStartLine: this.visualStartLine, visualEndLine: curLine });
      } else {
        this.deleteVisualCharRange();
        this.lastVisualStartLine = this.visualStartLine;
        this.lastVisualStartCol = this.visualStartCol;
        this.lastVisualEndLine = curLine;
        this.lastVisualEndCol = curCol;
        this.lastVisualType = "char";
        this.recordLastChange("visual", "d", 1, { visualType: "char",
          visualStartLine: this.visualStartLine, visualStartCol: this.visualStartCol,
          visualEndLine: curLine, visualEndCol: curCol });
      }
      this.mode = "NORMAL";
      return;
    }
    if (data === "c") {
      const curLine = this.getCursorLine0();
      this.saveUndoState();
      if (this._visualType === "line") {
        this.deleteLineRange(this.visualStartLine, curLine);
        this.recordLastChange("visual", "c", 1, { visualType: "line",
          visualStartLine: this.visualStartLine, visualEndLine: curLine });
      } else {
        this.deleteVisualCharRange();
        const curCol = this.getCursorCol0();
        this.recordLastChange("visual", "c", 1, { visualType: "char",
          visualStartLine: this.visualStartLine, visualStartCol: this.visualStartCol,
          visualEndLine: curLine, visualEndCol: curCol });
      }
      this.mode = "INSERT";
      return;
    }
    if (data === "y") {
      const curLine = this.getCursorLine0();
      if (this._visualType === "line") {
        this.yankLines(this.visualStartLine, curLine);
      } else {
        this.yankCharRange(this.visualStartLine, this.visualStartCol, curLine, this.getCursorCol0());
      }
      this.mode = "NORMAL";
      return;
    }
    if (data === ">" || data === "<") {
      const curLine = this.getCursorLine0();
      this.execLineOpRange(data as Operator, this.visualStartLine, curLine);
      this.mode = "NORMAL";
      return;
    }

    // ── { / }: paragraph motions in visual mode ──
    if (data === "{" || data === "}") {
      const count = 1;
      if (data === "{") this.motionPrevParagraph(count);
      else this.motionNextParagraph(count);
      this.syncState();
      this.tuiRef.requestRender();
      return;
    }

    // Motions in visual mode (extend selection)
    this.applyNormalMotion(data, 1, false);
    this.syncState();
    this.tuiRef.requestRender();
  }

  private deleteVisualCharRange() {
    const curLine = this.getCursorLine0();
    const curCol = this.getCursorCol0();
    const lines = this.getLines();

    if (this.visualStartLine === curLine) {
      const a = Math.min(this.visualStartCol, curCol);
      const b = Math.max(this.visualStartCol, curCol);
      const lineLen = lines[curLine].length;
      const endCol = Math.min(b, lineLen > 0 ? lineLen - 1 : 0);
      if (endCol < a) return;
      this.goToLineAbs(curLine);
      this.motionHome();
      this.motionRight(a);
      for (let i = a; i <= endCol; i++) this.deleteCharRightChars(1);
    } else {
      const s = Math.min(this.visualStartLine, curLine);
      const e = Math.max(this.visualStartLine, curLine);
      this.deleteLineRange(s, e);
    }
    this.syncState();
    this.tuiRef.requestRender();
  }

  // ───────────────────────────────────────────────────────────
  // COMMAND mode
  // ───────────────────────────────────────────────────────────

  private handleCommandInput(data: string) {
    if (matchesKey(data, Key.escape)) { this.mode = "NORMAL"; return; }
    if (matchesKey(data, Key.enter)) {
      this.executeCommand(this.commandBuffer);
      this.mode = "NORMAL";
      return;
    }
    if (matchesKey(data, Key.backspace)) {
      this.commandBuffer = this.commandBuffer.slice(0, -1);
      if (this.commandBuffer.length === 0) { this.mode = "NORMAL"; return; }
      this.syncState(); this.tuiRef.requestRender();
      return;
    }
    // Ctrl+R in command mode: insert yank buffer
    if (matchesKey(data, Key.ctrl("r"))) {
      this.commandBuffer += this.yankBuffer;
      this.syncState(); this.tuiRef.requestRender();
      return;
    }
    if (data.length === 1 && data.charCodeAt(0) >= 32 && data.charCodeAt(0) <= 126) {
      this.commandBuffer += data;
      this.syncState(); this.tuiRef.requestRender();
    }
  }

  private executeCommand(cmd: string) {
    const c = cmd.slice(1).trim();

    // :w — save prompt state
    if (c === "w") {
      this.saveState();
      return;
    }

    // :wq or :x — save + exit
    if (c === "wq" || c === "x") {
      this.saveState();
      this.cleanupAndExit();
      return;
    }

    // :q or :q! — exit
    if (c === "q" || c === "q!") {
      this.cleanupAndExit();
      return;
    }

    // :man — open vim.man in less
    if (c === "man") {
      const manPath = path.join(os.homedir(), ".pi", "agent", "extensions", "vim.man");
      try {
        // Leave raw mode so less can use the terminal normally
        if (process.stdin.isRaw) process.stdin.setRawMode(false);
        this.tuiRef.terminal.write("\x1b[0 q\x1b[?25h"); // reset cursor, show
        execSync(`less "${manPath}"`, { stdio: "inherit" });
      } catch {
        // less may exit with non-zero (q, etc.), that's fine
      } finally {
        // Re-enter raw mode and redraw
        if (!process.stdin.isRaw) process.stdin.setRawMode(true);
        this.tuiRef.terminal.write("\x1b[?25l"); // hide cursor (TUI manages it)
        this.tuiRef.requestRender();
      }
      return;
    }

    // :s/pattern/replacement/flags or :%s/pattern/replacement/flags
    if (c.startsWith("s") || c.startsWith("%s")) {
      this.doSubstitute(c);
      return;
    }

    // :!<cmd> — run bash command
    if (c.startsWith("!")) {
      this.setText(`!${c.slice(1)}`);
      this.submitText();
    }
  }

  /** Gracefully quit pi, restoring terminal settings properly. */
  private cleanupAndExit() {
    // Delegate to the shutdown callback if available (graceful pi shutdown)
    if (this.onQuit) {
      this.onQuit();
    } else {
      // Fallback: reset cursor shape and exit
      this.tuiRef.terminal.write("\x1b[0 q");
      setTimeout(() => process.exit(0), 50);
    }
  }

  private saveState() {
    try {
      const text = this.getText();
      const cursor = this.getCursor();
      const state: SavedState = {
        text,
        cursorLine: cursor.line,
        cursorCol: cursor.col,
      };
      fs.writeFileSync(STATE_PATH, JSON.stringify(state, null, 2), "utf-8");
    } catch (_e) {
      // silently ignore write errors
    }
  }

  private submitText() {
    const t = this.getText().trim();
    if (t) super.handleInput("\r");
  }

  // ───────────────────────────────────────────────────────────
  // Render
  // ───────────────────────────────────────────────────────────

  override render(width: number): string[] {
    this.tuiRef.setShowHardwareCursor(true);
    this.syncState();
    let lines = super.render(width);

    // Strip Editor's fake cursor highlight
    lines = lines.map(line => line.replace(/\x1b\[7m([^\x1b]*?)\x1b\[0m/g, "$1"));

    // ── VISUAL mode highlighting ──
    if (this._mode === "VISUAL" && this.visualStartLine >= 0) {
      const cur = this.getCursor();
      const rawLines = this.getLines();
      const startDoc = Math.min(this.visualStartLine, cur.line);
      const endDoc = Math.max(this.visualStartLine, cur.line);

      const paddingX = this.getPaddingX();
      const contentWidth = Math.max(1, width - 2 * paddingX);
      let visIdx = 0;
      const docToVis: Array<{ start: number; end: number }> = [];
      const visLineInfo: Array<{ docLine: number; startCol: number; endCol: number }> = [];
      for (let d = 0; d < rawLines.length; d++) {
        const chunks = wrapTextWithAnsi(rawLines[d], contentWidth);
        docToVis.push({ start: visIdx, end: visIdx + chunks.length - 1 });
        let colOff = 0;
        for (const ch of chunks) {
          visLineInfo.push({ docLine: d, startCol: colOff, endCol: colOff + visibleWidth(ch) });
          colOff += visibleWidth(ch);
        }
        visIdx += chunks.length;
      }

      const scrollOffset: number = (this as any).scrollOffset ?? 0;
      const topBorder = 1;
      const selVisStart = docToVis[startDoc]?.start ?? 0;
      const selVisEnd = docToVis[endDoc]?.end ?? 0;
      const selStart = topBorder + selVisStart - scrollOffset;
      const selEnd = topBorder + selVisEnd - scrollOffset;

      const isLineWise = this._visualType === "line";

      const docColStart = new Map<number, number>();
      const docColEnd   = new Map<number, number>();
      for (let d = startDoc; d <= endDoc; d++) {
        if (startDoc === endDoc) {
          const a = Math.min(this.visualStartCol, cur.col);
          const b = Math.max(this.visualStartCol, cur.col) + 1;
          docColStart.set(d, a); docColEnd.set(d, b);
        } else if (d === this.visualStartLine) {
          const forward = this.visualStartLine <= cur.line;
          docColStart.set(d, forward ? this.visualStartCol : 0);
          docColEnd.set(d,   forward ? Infinity : this.visualStartCol + 1);
        } else if (d === cur.line) {
          const forward = this.visualStartLine <= cur.line;
          docColStart.set(d, forward ? 0 : cur.col);
          docColEnd.set(d,   forward ? cur.col + 1 : Infinity);
        } else {
          docColStart.set(d, 0); docColEnd.set(d, Infinity);
        }
      }

      lines = lines.map((line, i) => {
        if (/^\x1b\[[0-9;]*m?─+\x1b\[m?$/.test(line.trimEnd())) return line;
        if (i < selStart || i > selEnd) return line;

        if (isLineWise) {
          return highlightEntireLine(line);
        }

        const infoIdx = selVisStart + (i - selStart);
        const info = visLineInfo[infoIdx];
        if (!info) return highlightEntireLine(line);

        const dcs = docColStart.get(info.docLine);
        const dce = docColEnd.get(info.docLine);
        if (dcs === undefined || dce === undefined) return line;

        const effEnd = dce === Infinity ? info.endCol : dce;
        const hlStart = Math.max(info.startCol, dcs);
        const hlEnd = Math.min(info.endCol, effEnd);
        if (hlStart >= hlEnd) return line;

        return highlightLineRange(line, hlStart - info.startCol, hlEnd - info.startCol);
      });
    }

    return lines;
  }

}

// ─────────────────────────────────────────────────────────────
// Visual highlighting helpers
// ─────────────────────────────────────────────────────────────

function skipEscape(line: string, i: number): number {
  if (i + 1 < line.length && line[i + 1] === '[') {
    for (let j = i + 2; j < line.length; j++) {
      if (line.charCodeAt(j) >= 0x40 && line.charCodeAt(j) <= 0x7E) return j + 1;
    }
    return line.length;
  }
  const bel = line.indexOf('\x07', i + 1);
  if (bel !== -1) return bel + 1;
  return i + 2;
}

function highlightEntireLine(line: string): string {
  const trimmed = line.trimEnd();
  if (!trimmed) return line;
  const pad = visibleWidth(line) - visibleWidth(trimmed);
  return `\x1b[7m${trimmed}\x1b[27m${' '.repeat(Math.max(0, pad))}`;
}

function highlightLineRange(line: string, startVisCol: number, endVisCol: number): string {
  const lineW = visibleWidth(line);
  const s = Math.max(0, Math.min(startVisCol, endVisCol));
  const e = Math.min(lineW, Math.max(startVisCol, endVisCol));
  if (s >= e || s >= lineW || e <= 0) return line;

  let result = '';
  let visPos = 0;
  let i = 0;

  while (i < line.length && visPos < s) {
    if (line[i] === '\x1b') {
      const end = skipEscape(line, i);
      result += line.substring(i, end);
      i = end;
    } else {
      result += line[i]; visPos++; i++;
    }
  }

  result += '\x1b[7m';

  while (i < line.length && visPos < e) {
    if (line[i] === '\x1b') {
      const end = skipEscape(line, i);
      result += line.substring(i, end);
      i = end;
    } else {
      result += line[i]; visPos++; i++;
    }
  }

  result += '\x1b[27m';
  result += line.substring(i);
  return result;
}

// ─────────────────────────────────────────────────────────────
// Extension entry point
// ─────────────────────────────────────────────────────────────

export default function (pi: ExtensionAPI) {
  pi.on("session_start", (event, ctx) => {
    ctx.ui.setWidget("vim-status", (_tui, theme) => ({
      render: (): string[] => {
        const w = _tui.terminal.columns;
        if (w < 24) return [];

        const { mode, line, totalLines: total, col, recording, commandBuffer: cmd, pendingCount: cnt } = vimState;

        const label =
          mode === "INSERT"  ? " INSERT " :
          mode === "NORMAL"  ? " NORMAL " :
          mode === "VISUAL"  ? " VISUAL " :
          " COMMAND ";

        const modeBg =
          mode === "INSERT"  ? theme.bg("toolSuccessBg", theme.fg("text", label)) :
          mode === "NORMAL"  ? theme.bg("selectedBg", theme.fg("accent", label)) :
          mode === "VISUAL"  ? theme.bg("toolSuccessBg", theme.fg("text", label)) :
          theme.bg("toolErrorBg", theme.fg("text", label));

        let cntStr = cnt ? theme.fg("warning", ` [${cnt}]`) : "";
        const pos = theme.fg("dim", ` Ln ${line}/${total}  Col ${col} `);
        const sep = theme.fg("muted", " │ ");

        let rec = "";
        if (typeof recording === "string") rec = theme.fg("warning", `  ● Rec @${recording}  `);

        let cmds = "";
        if (mode === "COMMAND" && cmd) cmds = theme.fg("accent", `  ${cmd}  `);

        let parts: string[];
        if (cntStr) {
          parts = [modeBg, cntStr, sep, pos];
        } else {
          parts = [modeBg, sep, pos];
        }
        if (rec) parts.push(rec);
        if (cmds) parts.push(cmds);

        let bar = parts.join("");
        if (visibleWidth(bar) < w) bar += " ".repeat(w - visibleWidth(bar));
        return [bar.slice(0, w)];
      },
      invalidate() {},
    }), { placement: "belowEditor" });

    ctx.ui.setEditorComponent((tui, theme, kb) => {
      const editor = new VimEditor(tui, theme, kb);
      editor.onQuit = () => ctx.shutdown();

      // Restore saved text from :w / :wq on session resume (not on new/fork).
      // Must defer because setEditorComponent overwrites the editor text with
      // the default editor's content after the factory returns.
      if (event.reason === "resume" || event.reason === "startup") {
        setTimeout(() => {
          try {
            const saved = JSON.parse(fs.readFileSync(STATE_PATH, "utf-8")) as SavedState;
            if (saved.text) {
              editor.setText(saved.text);
              const lines = editor.getLines();
              const targetLine = Math.min(saved.cursorLine, lines.length - 1);
              for (let i = 0; i < targetLine; i++) editor.handleInput("\x1b[B");
              const targetLineLen = lines[targetLine]?.length ?? 0;
              const targetCol = Math.min(saved.cursorCol, targetLineLen);
              for (let i = 0; i < targetCol; i++) editor.handleInput("\x1b[C");
            }
          } catch {}
        }, 0);
      }

      return editor;
    });
  });
}
