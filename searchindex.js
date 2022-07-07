Search.setIndex({"docnames": ["day1", "day2", "day3", "hint_1_barber_paradox", "hint_1_have_exercise", "hint_1_mcsp", "hint_1_negation_exercises", "hint_2_barber_paradox", "hint_2_have_exercise", "hint_2_mcsp", "hint_2_negation_exercises", "hint_3_negation_exercises", "index", "introduction", "symbols", "tactics"], "filenames": ["day1.rst", "day2.rst", "day3.rst", "hint_1_barber_paradox.rst", "hint_1_have_exercise.rst", "hint_1_mcsp.rst", "hint_1_negation_exercises.rst", "hint_2_barber_paradox.rst", "hint_2_have_exercise.rst", "hint_2_mcsp.rst", "hint_2_negation_exercises.rst", "hint_3_negation_exercises.rst", "index.rst", "introduction.rst", "symbols.rst", "tactics.rst"], "titles": ["<span class=\"section-number\">1. </span>Logic in Lean - Part 1", "<span class=\"section-number\">2. </span>Logic in Lean - Part 2", "<span class=\"section-number\">3. </span>Infinitely Many Primes", "Hint 1 for the barber paradox", "Hint 1 for the have exercise", "Hint 1 for the math campers singing paradox", "Hint 1 for Day 1 negation exercises", "Hint 2 for the barber paradox", "Hint 2 for the have exercise", "Hint 2 for the math campers singing paradox", "Hint 2 for Day 1 negation exercises", "Hint 3 for Day 1 negation exercises", "Lean at MC 2022", "Introduction", "Pretty Symbols in Lean", "Glossary of Tactics and Lemmas"], "terms": {"todai": [0, 1, 2], "s": [0, 1, 2, 13, 15], "goal": [0, 1, 2, 13, 15], "understand": [0, 1], "philosophi": 0, "theori": [0, 1, 2, 13], "don": [0, 1, 2], "t": [0, 1, 2, 15], "try": [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 15], "memor": 0, "anyth": [0, 15], "happen": 0, "automat": 0, "instead": [0, 2, 15], "do": [0, 1, 2, 13], "mani": [0, 12], "exercis": [0, 2, 13], "you": [0, 1, 2, 13, 14, 15], "can": [0, 1, 2, 13, 15], "practic": [0, 1], "onli": [0, 1, 2, 13, 14, 15], "wai": [0, 1, 15], "learn": [0, 2, 13], "new": [0, 1, 2], "program": 0, "languag": 0, "alwai": [0, 1, 2], "save": [0, 1, 2], "your": [0, 1, 2, 6, 10, 11, 13, 14, 15], "work": [0, 1, 2, 15], "The": [0, 2, 12, 13, 14, 15], "easiest": 0, "thi": [0, 1, 2, 13, 15], "browser": 0, "bookmark": 0, "page": [0, 1], "which": [0, 1, 2, 9, 13, 15], "contain": [0, 1, 2], "code": [0, 13], "its": [0, 1, 15], "url": 0, "built": [0, 13], "top": [0, 1, 13], "system": [0, 13], "call": [0, 1, 13], "an": [0, 1, 2, 13, 15], "altern": 0, "set": [0, 1, 2, 13, 15], "In": [0, 1, 2, 13], "element": [0, 1, 13, 15], "we": [0, 1, 2, 13, 15], "have": [0, 1, 2, 13, 15], "term": [0, 1, 2, 10, 13, 15], "everi": [0, 1, 2, 13], "ha": [0, 1, 2, 10, 13, 15], "when": [0, 2, 15], "translat": [0, 15], "math": [0, 1, 2], "either": [0, 1], "mathemat": [0, 1, 13, 15], "object": [0, 13], "function": [0, 13, 14, 15], "proof": [0, 2, 13], "notat": 0, "x": [0, 1, 13, 15], "stand": [0, 1], "inhabit": [0, 1], "For": [0, 1, 2, 15], "most": [0, 2], "think": [0, 1], "ani": [0, 1], "statement": [0, 1, 2], "potenti": 0, "being": [0, 1, 2], "true": [0, 1, 2, 15], "fals": [0, 1, 10, 11, 15], "like": [0, 13, 15], "2": [0, 2, 12, 13, 15], "4": [0, 2, 13, 15], "5": [0, 13], "fermat": 0, "last": 0, "theorem": [0, 1, 2, 13, 15], "riemann": 0, "hypothesi": [0, 1, 2, 15], "special": [0, 1, 13], "prop": [0, 1, 15], "whose": 0, "ar": [0, 1, 2, 10, 13, 15], "furthermor": 0, "each": [0, 13, 15], "p": [0, 1, 2, 15], "itself": [0, 1], "hp": [0, 1, 2, 10, 15], "As": [0, 1, 2], "produc": [0, 14, 15], "same": [0, 1, 2, 13, 15], "so": [0, 1, 2, 13, 15], "exist": [0, 1, 14], "throughout": 0, "note": [0, 1, 2], "q": [0, 1, 2, 6, 10, 11, 15], "r": [0, 1, 15], "denot": 0, "written": [0, 2], "us": [0, 1, 2, 6, 9, 14, 15], "follow": [0, 1, 2, 13, 14], "syntax": 0, "fermats_last_theorem": 0, "n": [0, 1, 2, 13, 15], "\u2115": [0, 1, 2, 13, 14, 15], "n_gt_2": 0, "y": [0, 1, 13, 15], "z": [0, 1, 13], "0": [0, 1, 2, 13, 15], "begin": [0, 1, 2, 13], "sorri": [0, 1, 2, 5, 7, 9, 13], "end": [0, 1, 2, 13, 15], "let": [0, 1, 15], "pars": 0, "abov": [0, 1], "ignor": 0, "multipl": [0, 1, 2], "whitespac": 0, "tab": [0, 14], "line": [0, 1, 2, 13], "could": [0, 15], "theoret": 0, "write": [0, 2, 13], "entir": 0, "singl": [0, 1, 2], "pleas": 0, "name": [0, 13, 15], "two": [0, 2, 10, 13, 15], "hypothes": [0, 2, 10, 15], "former": 0, "sai": [0, 1, 2, 15], "natur": [0, 1, 2, 13, 14, 15], "number": [0, 1, 2, 13, 14, 15], "latter": 0, "delimit": 0, "between": [0, 2], "target": [0, 1, 2, 6, 11, 15], "ll": [0, 2, 13, 15], "all": [0, 1, 13, 14, 15], "symbol": [0, 1, 2, 12, 15], "soon": 0, "start": [0, 1, 2], "open": [0, 1, 2, 13], "up": [0, 1, 2, 15], "window": [0, 2, 13, 15], "keep": [0, 1], "track": [0, 1], "exampl": [0, 1, 2, 13, 15], "command": [0, 13], "tactic": [0, 1, 2, 9, 12, 13, 14], "veri": [0, 1, 2, 13, 14, 15], "import": [0, 1, 2, 13, 15], "must": 0, "comma": 0, "even": [0, 2], "though": 0, "thei": [0, 1, 2], "explicitli": [0, 2], "displai": 0, "librari": [0, 2, 15], "also": [0, 1, 2, 13, 15], "close": [0, 1, 2, 15], "impli": [0, 1, 14, 15], "both": [0, 2], "just": [0, 1, 2, 13], "f": [0, 1, 2, 13, 15], "given": [0, 1, 15], "If": [0, 1, 2, 6, 10, 11, 13, 15], "empti": [0, 1], "from": [0, 1, 2, 9, 13, 15], "henc": 0, "editor": [0, 14], "prove": [0, 1, 2, 13], "section": 0, "tabl": 0, "describ": 0, "what": [0, 1, 2, 15], "doe": [0, 15], "solv": [0, 2], "see": [0, 1, 2, 13, 15], "action": 0, "first": [0, 2, 15], "refin": [0, 1, 2, 11, 15], "rintro": [0, 1, 3, 6, 7, 15], "current": [0, 1, 15], "were": [0, 15], "requir": [0, 1, 2, 15], "chang": [0, 1, 2, 15], "order": [0, 15], "defin": [0, 1, 2, 15], "need": [0, 1, 2, 3, 4, 5, 6, 10, 15], "choos": [0, 2, 15], "introduc": [0, 15], "arbitrari": [0, 15], "want": [0, 1, 15], "repeatedli": [0, 15], "h1": [0, 1, 3, 7, 15], "h2": [0, 1, 3, 7, 15], "delet": [0, 1, 2], "below": [0, 1, 2], "replac": [0, 1, 2, 15], "them": [0, 1, 2], "legitim": [0, 1, 2], "tautolog": [0, 1], "find": [0, 1], "differ": [0, 1, 2, 15], "know": [0, 1, 2], "how": [0, 1, 2], "finish": 0, "about": [0, 1, 2, 13], "partial": 0, "progress": 0, "here": [0, 1, 2, 15], "approach": 0, "One": [0, 13, 15], "forward": 0, "reason": [0, 15], "other": [0, 1, 2, 15], "again": 0, "backward": [0, 15], "case": [0, 1, 2, 3, 5, 7, 9, 15], "send": 0, "liter": [0, 15], "although": [0, 1], "often": [0, 1, 2, 15], "skip": 0, "parenthes": 0, "creat": [0, 1, 12, 13, 15], "intermedi": [0, 15], "variabl": [0, 1, 15], "hq": [0, 1, 2, 6, 15], "_": [0, 11, 15], "equival": [0, 1, 15], "becaus": [0, 1, 15], "suffic": [0, 15], "provid": [0, 1, 2, 13, 15], "later": [0, 1, 2], "interchang": [0, 1], "big": 0, "healthi": 0, "combin": [0, 1, 15], "make": [0, 1, 2, 9], "readabl": [0, 2], "g": [0, 1, 15], "u": 0, "hpq": [0, 15], "hqr": 0, "hqt": 0, "hst": 0, "htu": 0, "lot": [0, 2, 13], "week": 0, "ever": [0, 15], "lose": 0, "check": [0, 1, 2, 13], "out": [0, 2, 14], "glossari": [0, 1, 9, 12], "list": 0, "mention": [0, 1], "well": [0, 15], "some": [0, 1, 13, 15], "class": [0, 13, 15], "mai": [0, 1, 15], "come": 0, "read": [0, 1, 2, 13], "oper": [0, 1, 2, 13, 14, 15], "easi": [0, 1], "vice": 0, "versa": 0, "similarli": [0, 2], "subtl": 0, "topmost": 0, "after": [0, 1], "should": [0, 2, 13, 15], "off": 0, "attempt": [0, 13], "second": [0, 15], "Then": [0, 15], "put": 0, "cursor": 0, "monitor": 0, "right": [0, 1, 2, 13, 15], "one": [0, 1, 2, 11, 13, 15], "time": [0, 1, 2], "gener": [0, 1, 15], "break": [0, 1, 2, 15], "complic": [0, 1, 2, 14, 15], "simpler": [0, 2, 15], "ones": [0, 15], "fg": [0, 15], "actual": [0, 1], "shorthand": 0, "add": [0, 1, 2, 15], "split": [0, 15], "left": [0, 1, 15], "wise": 0, "bracket_exampl": 0, "ve": 0, "discuss": 0, "build": [0, 14], "pretti": [0, 1, 2, 12, 15], "much": [0, 15], "thing": [0, 1, 2, 13, 15], "seen": [0, 1, 2], "howev": [0, 2], "directli": [0, 1], "angl": 0, "langl": [0, 14, 15], "rangl": [0, 14, 15], "pair": 0, "consist": 0, "explor": 0, "rewrit": [0, 1, 15], "Such": 0, "justifi": 0, "definit": [0, 1, 2, 14, 15], "To": [0, 1, 2, 14], "summar": 0, "recal": [0, 1], "hint": [0, 1, 2], "get": [0, 1, 2, 13, 15], "stuck": [0, 1], "self_imp_not_not_self": 0, "contraposit": [0, 15], "now": [0, 2], "re": [0, 1, 2, 15], "talk": [0, 1], "everybodi": 0, "favorit": 0, "least": [0, 1, 2, 13], "techniqu": 0, "contradict": [0, 1], "version": 0, "principl": 0, "explos": 0, "deriv": [0, 15], "fact": [0, 1, 2, 15], "whenev": [0, 2], "elim": [0, 1, 15], "principle_of_explos": [0, 1], "might": [0, 1, 2], "wonder": 0, "cool": 0, "why": [0, 1], "i": 0, "heard": 0, "befor": [0, 1], "highli": 0, "depend": [0, 1], "where": [0, 15], "datatyp": 0, "onc": [0, 1, 13, 15], "comput": [0, 2], "immedi": 0, "manipul": [0, 2, 15], "valid": 0, "accident": 0, "divid": [0, 2], "unfortun": 0, "mean": [0, 1, 13], "\u2124": [0, 14], "subtract": 0, "buddi": 0, "anoth": [0, 13], "issu": 0, "world": [0, 13], "allow": 0, "coerc": 0, "properli": 0, "\u211a": 0, "divis": [0, 12, 14], "few": 0, "drive": 0, "mathematician": [0, 1], "awai": [0, 15], "But": [0, 2], "difficult": 0, "With": 0, "becom": 0, "exact": [0, 1, 15], "equiconsist": 0, "slightli": [0, 2], "stronger": 0, "zfc": 0, "accept": 0, "axiom": [0, 1, 2], "mario": 0, "carneiro": 0, "ms": 0, "thesi": 0, "footnot": [0, 14], "except": 0, "under": [0, 1], "staff": [0, 13], "supervis": 0, "wrap": 1, "remain": 1, "bit": 1, "move": 1, "rememb": [1, 2, 15], "stuff": 1, "did": 1, "yesterdai": 1, "A": 1, "bracket": 1, "It": [1, 2, 13, 15], "uncommon": 1, "compos": 1, "half": 1, "dozen": 1, "realli": [1, 15], "messi": 1, "unwieldi": 1, "drop": 1, "convent": 1, "express": [1, 2, 15], "b": [1, 2, 15], "c": [1, 2], "d": [1, 2], "arrow": 1, "binari": 1, "feel": 1, "weird": 1, "proposit": [1, 2, 12, 13], "huge": 1, "seem": 1, "unnecessari": 1, "someth": [1, 15], "normal": 1, "hide": 1, "type": [1, 2, 10, 12, 13, 14, 15], "hp1": 1, "hp2": 1, "take": [1, 2], "our": [1, 2], "analog": 1, "further": 1, "form": [1, 15], "e": 1, "homotopi": 1, "taken": [1, 13], "cours": [1, 13], "1": [1, 2, 8, 12, 13, 14, 15], "successfulli": 1, "construct": [1, 2], "purpos": [1, 15], "classic": [1, 2], "sens": 1, "word": [1, 2], "codomain": 1, "input": [1, 2], "consid": [1, 2], "hello_world": 1, "hr": [1, 15], "conveni": 1, "lack": 1, "simul": 1, "forget": 1, "content": 1, "fall": 1, "giant": 1, "umbrella": 1, "curri": 1, "howard": 1, "correspond": [1, 2], "speak": 1, "without": [1, 2], "\u03bb": 1, "plai": [1, 13], "basic": [1, 2, 13, 15], "role": 1, "give": 1, "output": 1, "instanc": [1, 15], "addit": [1, 2], "around": [1, 15], "exactli": [1, 2], "three": 1, "not_not_self_imp_self": 1, "contrapositive_convers": 1, "drastic": 1, "There": 1, "extra": 1, "em": [1, 5, 7, 9, 15], "includ": 1, "would": [1, 2, 15], "prefer": 1, "avoid": [1, 15], "noncomput": [1, 2], "open_local": [1, 2], "file": 1, "show": [1, 2], "ok": 1, "more": [1, 2, 3, 4, 5, 6, 10, 15], "streamlin": 1, "process": [1, 13], "deal": [1, 2, 9], "negat": [1, 9, 12, 14], "shorten": 1, "introduct": [1, 12], "those": 1, "foral": [1, 14], "hpy": [1, 15], "similar": [1, 13, 15], "tool": 1, "wit": [1, 15], "extract": 1, "kei": [1, 5, 9, 15], "tri": [1, 2, 15], "final": [1, 12], "enough": [1, 2], "fun": [1, 13], "disprov": 1, "due": 1, "bertrand": 1, "russel": 1, "claim": 1, "certain": 1, "town": 1, "male": 1, "shave": [1, 7], "men": 1, "who": 1, "themselv": 1, "man": 1, "assum": 1, "main": 1, "loung": 1, "non": [1, 2], "At": 1, "fix": 1, "moment": 1, "someon": 1, "everyon": 1, "camper": [1, 13], "math_campers_singing_paradox": 1, "alic": 1, "sure": 1, "relat": [1, 2], "map": 1, "reflex": 1, "symmetr": 1, "transit": 1, "connect": [1, 2], "reflexive_of_symmetric_transitive_and_connect": 1, "h_symm": 1, "h_tran": 1, "h_connect": 1, "far": [1, 2], "hand": [1, 2], "mess": 1, "usual": [1, 2], "rw": [1, 2, 13, 14, 15], "side": 1, "search": [1, 15], "addition": [1, 15], "l": [1, 14], "bunch": 1, "row": 1, "h3": 1, "data": [1, 2, 13], "nat": [1, 2, 13, 14, 15], "variant": 1, "add_self_self_eq_doubl": 1, "two_mul": 1, "problem": [1, 2], "mul_comm": 1, "hyp": 1, "sub_self": 1, "hard": 1, "h": [1, 3, 7, 15], "rid": 1, "unfold": [1, 15], "everywher": 1, "comp_app": 1, "hf": 1, "hg": 1, "hgf": 1, "mathlib": [2, 15], "focu": 2, "go": [2, 13], "lean": 2, "k": [2, 15], "simpli": 2, "warn": 2, "mid": [2, 14], "vertic": 2, "keyboard": [2, 14], "littl": 2, "back": 2, "prime_def_lt": 2, "m": [2, 15], "101": 2, "possibl": 2, "down": 2, "rabbit": 2, "hole": 2, "exhaust": 2, "kind": [2, 13], "rather": 2, "autom": 2, "norm_num": [2, 15], "involv": [2, 15], "arithmet": [2, 15], "power": 2, "assumpt": [2, 11, 15], "simplifi": [2, 13, 15], "ring_nf": [2, 15], "algebra": [2, 15], "linarith": [2, 15], "inequ": [2, 15], "solver": [2, 15], "sometim": 2, "aren": 2, "2020": [2, 13], "long": 2, "done": 2, "origin": 2, "alreadi": [2, 15], "intern": 2, "crucial": 2, "abl": 2, "match": 2, "hn": 2, "hn2": 2, "lemma": [2, 12], "dvd_sub": 2, "infer": 2, "rest": 2, "tomorrow": 2, "dvd_sub_on": 2, "strategi": 2, "greater": 2, "than": 2, "smallest": 2, "factor": 2, "not_dvd_on": 2, "factori": 2, "factorial_po": 2, "dvd_factori": 2, "min_fac": 2, "min_fac_prim": 2, "min_fac_po": 2, "min_fac_dvd": 2, "step": 2, "sketch": 2, "paper": 2, "lost": 2, "exists_infinite_prim": 2, "abbrevi": [2, 15], "great": [2, 13], "wa": 2, "leav": 2, "detail": [2, 13], "realiz": 2, "expect": 2, "reader": 2, "intellig": 2, "fill": [2, 15], "bug": 2, "featur": [2, 13], "On": [2, 13], "too": 2, "obvious": 2, "argument": 2, "undecipher": 2, "wrong": 2, "unlik": 2, "human": 2, "dumb": 2, "tell": 2, "cannot": 2, "humanli": 2, "imposs": 2, "teach": [2, 13], "collect": 2, "comprehens": [2, 13], "scan": 2, "sadli": 2, "harder": 2, "small": 2, "frequent": 2, "goe": 2, "hope": 2, "ai": 2, "eventu": 2, "elimin": 2, "machin": 2, "h_le": 4, "bob": [5, 9], "hye": [5, 7, 9], "hno": [5, 7, 9], "h_one": 8, "push_neg": [9, 15], "easier": 9, "hnp": 10, "hnq": [11, 15], "logic": 12, "part": [12, 15], "implic": 12, "And": 12, "Or": 12, "remark": 12, "behind": 12, "scene": 12, "law": [12, 15], "exclud": [12, 15], "middl": [12, 15], "quantifi": [12, 14], "equal": [12, 14], "infinit": 12, "prime": [12, 13], "trivial": 12, "calcul": [12, 15], "subgoal": [12, 15], "sourc": 13, "checker": 13, "assist": 13, "explain": 13, "correct": 13, "formal": 13, "notion": 13, "compar": 13, "interpret": 13, "By": 13, "iter": 13, "verifi": 13, "complex": [13, 15], "def": 13, "3": 13, "easy_theorem_stat": 13, "fermats_last_theorem_stat": 13, "easy_proof": 13, "easy_theorem": 13, "hard_proof": 13, "cheat": 13, "while": 13, "snippet": 13, "eval": 13, "hello": 13, "click": [13, 15], "button": 13, "upper": 13, "corner": 13, "copi": 13, "edit": 13, "feedback": 13, "infoview": 13, "inlin": 13, "recommend": 13, "along": 13, "instal": 13, "download": 13, "ask": 13, "help": 13, "leanproject": 13, "awainvers": 13, "mc2022": 13, "folder": 13, "vscode": 13, "These": 13, "design": 13, "dai": 13, "crash": 13, "mathcamp": 13, "2022": 13, "base": [13, 15], "increasingli": 13, "infinitud": 13, "irration": 13, "sqrt": 13, "sneak": 13, "peek": 13, "simultan": 13, "option": 13, "game": 13, "properti": [13, 15], "onlin": 13, "book": 13, "aim": 13, "cover": 13, "aspect": 13, "commun": 13, "welcom": 13, "newcom": 13, "peopl": 13, "avail": 13, "zulip": 13, "chat": 13, "group": 13, "round": 13, "clock": 13, "answer": 13, "question": 13, "join": 13, "kevin": 13, "buzzard": 13, "discord": 13, "server": 13, "rel": 13, "younger": 13, "crowd": 13, "develop": 13, "aaron": 13, "anderson": 13, "updat": 13, "apurva": 13, "nakad": 13, "jalex": 13, "stark": 13, "joanna": 13, "maya": 13, "larg": 13, "chunk": 13, "variou": 13, "resourc": 13, "leanprov": 13, "websit": 13, "100": 13, "articl": 13, "video": 13, "blog": 13, "post": 13, "etc": 13, "xena": 13, "project": 13, "mechan": 13, "futur": 13, "twitch": 13, "channel": 13, "particular": 13, "checkout": 13, "summer": 13, "shortcut": 14, "space": 14, "unicod": 14, "iff": 14, "int": 14, "integ": 14, "circ": 14, "composit": 14, "ne": 14, "simpl": 14, "Be": 14, "care": 14, "through": 14, "cryptic": 14, "error": 14, "summari": 15, "common": 15, "encount": 15, "fulli": 15, "somewhat": 15, "miss": 15, "piec": 15, "appli": 15, "x1": 15, "x2": 15, "x3": 15, "separ": 15, "dispos": 15, "meanwhil": 15, "hx": 15, "accomplish": 15, "rcase": 15, "hmn": 15, "hme0": 15, "compon": 15, "Not": 15, "exfalso": 15, "ex": 15, "falso": 15, "quodlibet": 15, "contradictori": 15, "present": 15, "by_cas": 15, "by_contradict": 15, "essenti": 15, "push": 15, "across": 15, "contrapos": 15, "enter": 15, "refl": 15, "simp": 15, "behavior": 15, "ad": 15, "doesn": 15, "squeeze_simp": 15, "instruct": 15, "surject": 15, "ih": 15, "succ": 15, "succ_eq_add_on": 15, "handl": 15}, "objects": {}, "objtypes": {}, "objnames": {}, "titleterms": {"logic": [0, 1], "lean": [0, 1, 12, 13, 14, 15], "part": [0, 1], "1": [0, 3, 4, 5, 6, 10, 11], "proposit": 0, "type": 0, "implic": [0, 15], "And": [0, 15], "Or": [0, 15], "option": [0, 1], "sidenot": [0, 1], "bracket": 0, "negat": [0, 6, 10, 11, 15], "final": [0, 2], "remark": [0, 2], "2": [1, 7, 8, 9, 10], "behind": 1, "scene": 1, "proof": [1, 15], "irrelev": 1, "function": 1, "lambda": 1, "The": 1, "law": 1, "exclud": 1, "middl": 1, "quantifi": [1, 15], "barber": [1, 3, 7], "paradox": [1, 3, 5, 7, 9], "mathcamp": 1, "sing": [1, 5, 9], "relationship": 1, "conundrum": 1, "equal": [1, 15], "surject": 1, "infinit": 2, "mani": 2, "prime": 2, "divis": 2, "trivial": [2, 15], "calcul": 2, "creat": 2, "subgoal": 2, "hint": [3, 4, 5, 6, 7, 8, 9, 10, 11], "have": [4, 8], "exercis": [4, 6, 8, 10, 11], "math": [5, 9], "camper": [5, 9], "dai": [6, 10, 11], "3": 11, "mc": 12, "2022": 12, "introduct": 13, "what": 13, "how": 13, "us": 13, "note": 13, "acknowledg": 13, "link": 13, "pretti": 14, "symbol": 14, "glossari": 15, "tactic": 15, "lemma": 15, "contradict": 15, "prove": 15, "statement": 15, "induct": 15}, "envversion": {"sphinx.domains.c": 2, "sphinx.domains.changeset": 1, "sphinx.domains.citation": 1, "sphinx.domains.cpp": 6, "sphinx.domains.index": 1, "sphinx.domains.javascript": 2, "sphinx.domains.math": 2, "sphinx.domains.python": 3, "sphinx.domains.rst": 2, "sphinx.domains.std": 2, "sphinx.ext.todo": 2, "sphinx": 56}})