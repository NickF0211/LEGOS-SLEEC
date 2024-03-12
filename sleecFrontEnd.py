import sys
from os.path import dirname, join
sys.path.append(join(dirname(__file__), "Analyzer"))

import idlelib.colorizer as ic
import idlelib.percolator as ip
import re
import tkinter as tk
from sleecParser import check_input_red, check_input_conflict, check_input_concerns, check_input_purpose
from SleecNorm import check_situational_conflict


def read_model_file(file_path):
    with open(file_path, 'r') as file:
        return file.read()


def check_concern():
    cur_text = aText.get("1.0", 'end-1c')
    result, response, hl = check_input_concerns(cur_text)
    new_text.delete('1.0', 'end-1c')
    if result:
        new_text.insert(tk.INSERT, response)
    new_text.grid()


def check_situational():
    cur_text = aText.get("1.0", 'end-1c')
    result, response, hl = check_situational_conflict(cur_text)
    new_text.delete('1.0', 'end-1c')
    if result:
        cur_index = 0
        sorted_hl = sorted(hl, key=lambda k: k[0], reverse=True)
        while sorted_hl:
            cur_start, cur_end = sorted_hl.pop()
            if cur_start >= cur_index:
                new_text.insert(tk.INSERT, response[cur_index: cur_start])
                new_text.insert(tk.INSERT, response[cur_start: cur_end], "hl")
                cur_index = cur_end
        if cur_index < len(response):
            new_text.insert(tk.INSERT, response[cur_index:])
    else:
        new_text.insert(tk.INSERT, response)
    new_text.grid()


def check_redundancy():
    cur_text = aText.get("1.0", 'end-1c')
    result, response, hl = check_input_red(cur_text)
    new_text.delete('1.0', 'end-1c')
    if result:
        cur_index = 0
        sorted_hl = sorted(hl, key=lambda k: k[0], reverse=True)
        while sorted_hl:
            cur_start, cur_end = sorted_hl.pop()
            if cur_start >= cur_index:
                new_text.insert(tk.INSERT, response[cur_index: cur_start])
                new_text.insert(tk.INSERT, response[cur_start: cur_end], "hl")
                cur_index = cur_end
        if cur_index < len(response):
            new_text.insert(tk.INSERT, response[cur_index:])
    else:
        new_text.insert(tk.INSERT, response)
    new_text.grid()


def check_conflict():
    cur_text = aText.get("1.0", 'end-1c')
    result, response, hl = check_input_conflict(cur_text)
    new_text.delete('1.0', 'end-1c')
    if result:
        cur_index = 0
        sorted_hl = sorted(hl, key=lambda k: k[0], reverse=True)
        while sorted_hl:
            cur_start, cur_end = sorted_hl.pop()
            if cur_start >= cur_index:
                new_text.insert(tk.INSERT, response[cur_index: cur_start])
                new_text.insert(tk.INSERT, response[cur_start: cur_end], "hl")
                cur_index = cur_end
        if cur_index < len(response):
            new_text.insert(tk.INSERT, response[cur_index:])
    else:
        new_text.insert(tk.INSERT, response)
    new_text.grid()


def check_purpose():
    cur_text = aText.get("1.0", 'end-1c')
    result, response, hl = check_input_purpose(cur_text)
    new_text.delete('1.0', 'end-1c')
    if result:
        cur_index = 0
        sorted_hl = sorted(hl, key=lambda k: k[0], reverse=True)
        while sorted_hl:
            cur_start, cur_end = sorted_hl.pop()
            if cur_start >= cur_index:
                new_text.insert(tk.INSERT, response[cur_index: cur_start])
                new_text.insert(tk.INSERT, response[cur_start: cur_end], "hl")
                cur_index = cur_end
        if cur_index < len(response):
            new_text.insert(tk.INSERT, response[cur_index:])
    else:
        new_text.insert(tk.INSERT, response)
    new_text.grid()


sample_text = read_model_file("test.sleec")

# sample_text = "First line of text \nSecond line of text \nThird line of text"

lord = tk.Tk()
lord.title("SLEEC-D")

KEYWORD = r"\b(?P<KEYWORD>event|measure|constant|when|then|within|minutes|hours|seconds|unless|otherwise|boolean|numeric|scale|not|and|or|def_start|def_end|rule_end|rule_start|concern_start|concern_end|purpose_start|purpose_end|True|False|def_start|def_end|eventually|else|exists|while|meanwhile|invariant|witness|coincide|conflict|happenBefore|relation_start|relation_end|negate|imply|iff|negate|causation|effect|until|for|includes|forbid|mutualExclusive)\b"

# KEYWORD   = r"\b(?P<KEYWORD>False|None|True|and|as|assert|async|await|break|class|continue|def|del|elif|else|except|finally|for|from|global|if|import|in|is|lambda|nonlocal|not|or|pass|raise|return|try|while|with|yield)\b"
EXCEPTION = r"([^.'\"\\#]\b|^)(?P<EXCEPTION>ArithmeticError|AssertionError|AttributeError|BaseException|BlockingIOError|BrokenPipeError|BufferError|BytesWarning|ChildProcessError|ConnectionAbortedError|ConnectionError|ConnectionRefusedError|ConnectionResetError|DeprecationWarning|EOFError|Ellipsis|EnvironmentError|Exception|FileExistsError|FileNotFoundError|FloatingPointError|FutureWarning|GeneratorExit|IOError|ImportError|ImportWarning|IndentationError|IndexError|InterruptedError|IsADirectoryError|KeyError|KeyboardInterrupt|LookupError|MemoryError|ModuleNotFoundError|NameError|NotADirectoryError|NotImplemented|NotImplementedError|OSError|OverflowError|PendingDeprecationWarning|PermissionError|ProcessLookupError|RecursionError|ReferenceError|ResourceWarning|RuntimeError|RuntimeWarning|StopAsyncIteration|StopIteration|SyntaxError|SyntaxWarning|SystemError|SystemExit|TabError|TimeoutError|TypeError|UnboundLocalError|UnicodeDecodeError|UnicodeEncodeError|UnicodeError|UnicodeTranslateError|UnicodeWarning|UserWarning|ValueError|Warning|WindowsError|ZeroDivisionError)\b"
BUILTIN = r"([^.'\"\\#]\b|^)(?P<BUILTIN>abs|all|any|ascii|bin|breakpoint|callable|chr|classmethod|compile|complex|copyright|credits|delattr|dir|divmod|enumerate|eval|exec|exit|filter|format|frozenset|getattr|globals|hasattr|hash|help|hex|id|input|isinstance|issubclass|iter|len|license|locals|map|max|memoryview|min|next|oct|open|ord|pow|print|quit|range|repr|reversed|round|set|setattr|slice|sorted|staticmethod|sum|type|vars|zip)\b"
DOCSTRING = r"(?P<DOCSTRING>(?i:r|u|f|fr|rf|b|br|rb)?'''[^'\\]*((\\.|'(?!''))[^'\\]*)*(''')?|(?i:r|u|f|fr|rf|b|br|rb)?\"\"\"[^\"\\]*((\\.|\"(?!\"\"))[^\"\\]*)*(\"\"\")?)"
STRING = r"(?P<STRING>(?i:r|u|f|fr|rf|b|br|rb)?'[^'\\\n]*(\\.[^'\\\n]*)*'?|(?i:r|u|f|fr|rf|b|br|rb)?\"[^\"\\\n]*(\\.[^\"\\\n]*)*\"?)"
TYPES = r"\b(?P<TYPES>bool|bytearray|bytes|dict|float|int|list|str|tuple|object)\b"
NUMBER = r"\b(?P<NUMBER>((0x|0b|0o|#)[\da-fA-F]+)|((\d*\.)?\d+))\b"
CLASSDEF = r"(?<=\bclass)[ \t]+(?P<CLASSDEF>\w+)[ \t]*[:\(]"  # recolor of DEFINITION for class definitions
DECORATOR = r"(^[ \t]*(?P<DECORATOR>@[\w\d\.]+))"
INSTANCE = r"\b(?P<INSTANCE>super|self|cls)\b"
COMMENT = r"(?P<COMMENT>//[^\n]*)"
SYNC = r"(?P<SYNC>\n)"

PROG = rf"{KEYWORD}|{BUILTIN}|{EXCEPTION}|{TYPES}|{COMMENT}|{DOCSTRING}|{STRING}|{SYNC}|{INSTANCE}|{DECORATOR}|{NUMBER}|{CLASSDEF}"
IDPROG = r"(?<!class)\s+(\w+)"

TAGDEFS = {
    'COMMENT': {'foreground': "#013220", 'background': None, 'font': "Helvetica 14 bold"},
    # 'TYPES'      : {'foreground': CLOUD2    , 'background': None},
    'NUMBER': {'foreground': "#ffa500", 'font': "Helvetica 14 bold"},
    # 'BUILTIN'    : {'foreground': OVERCAST  , 'background': None},
    # 'STRING'     : {'foreground': PUMPKIN   , 'background': None},
    # 'DOCSTRING'  : {'foreground': STORMY    , 'background': None},
    # 'EXCEPTION'  : {'foreground': CLOUD2    , 'background': None, 'font':FONTBOLD},
    # 'DEFINITION' : {'foreground': SAILOR    , 'background': None, 'font':FONTBOLD},
    # 'DECORATOR'  : {'foreground': CLOUD2    , 'background': None, 'font':FONTITAL},
    # 'INSTANCE'   : {'foreground': CLOUD     , 'background': None, 'font':FONTITAL},
    'KEYWORD': {'foreground': '#8e44ad', 'font': "Helvetica 14 bold"},
    # 'CLASSDEF'   : {'foreground': PURPLE    , 'background': None, 'font':FONTBOLD},
}

cd = ic.ColorDelegator()
cd.prog = re.compile(PROG, re.S | re.M)
cd.idprog = re.compile(IDPROG, re.S)
cd.tagdefs = {**cd.tagdefs, **TAGDEFS}

cd1 = ic.ColorDelegator()
cd1.prog = re.compile(PROG, re.S | re.M)
cd1.idprog = re.compile(IDPROG, re.S)
cd1.tagdefs = {**cd.tagdefs, **TAGDEFS}

width = lord.winfo_screenwidth()
height = lord.winfo_screenheight()
lord_width = width // 3 * 2
lord_height = height
lord.geometry('%sx%s' % (lord_width, lord_height))

aText = tk.Text(lord, font=("Georgia", "14"))
aText.pack(expand=True, fill=tk.BOTH)
aText.insert(tk.INSERT, sample_text)
aText.grid()
ip.Percolator(aText).insertfilter(cd)

new_text = tk.Text(lord, font=("Georgia", "14"))
new_text.tag_config("hl", background="yellow")
ip.Percolator(new_text).insertfilter(cd1)

aButton = tk.Button(lord, text="check redundancy", command=check_redundancy)
aButton.grid()

bButton = tk.Button(lord, text="check conflicts", command=check_conflict)
bButton.grid()

bButton = tk.Button(lord, text="check concern", command=check_concern)
bButton.grid()

bButton = tk.Button(lord, text="check purpose", command=check_purpose)
bButton.grid()

bButton = tk.Button(lord, text="check situational conflict", command=check_situational)
bButton.grid()

aText.tag_config("bt", background="yellow")

lord.mainloop()
