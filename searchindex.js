Search.setIndex({"docnames": ["day1", "day2", "day3", "day4", "day5", "hint_1_barber_paradox", "hint_1_have_exercise", "hint_1_mcsp", "hint_1_negation_exercises", "hint_2_barber_paradox", "hint_2_have_exercise", "hint_2_mcsp", "hint_2_negation_exercises", "hint_3_negation_exercises", "index", "introduction", "symbols", "tactics"], "filenames": ["day1.rst", "day2.rst", "day3.rst", "day4.rst", "day5.rst", "hint_1_barber_paradox.rst", "hint_1_have_exercise.rst", "hint_1_mcsp.rst", "hint_1_negation_exercises.rst", "hint_2_barber_paradox.rst", "hint_2_have_exercise.rst", "hint_2_mcsp.rst", "hint_2_negation_exercises.rst", "hint_3_negation_exercises.rst", "index.rst", "introduction.rst", "symbols.rst", "tactics.rst"], "titles": ["<span class=\"section-number\">1. </span>Logic in Lean - Part 1", "<span class=\"section-number\">2. </span>Logic in Lean - Part 2", "<span class=\"section-number\">3. </span>Infinitely Many Primes", "<span class=\"section-number\">4. </span>Sqrt 2 is irrational", "<span class=\"section-number\">5. </span>Bits &amp; Pieces", "Hint 1 for the barber paradox", "Hint 1 for the have exercise", "Hint 1 for the math campers singing paradox", "Hint 1 for Day 1 negation exercises", "Hint 2 for the barber paradox", "Hint 2 for the have exercise", "Hint 2 for the math campers singing paradox", "Hint 2 for Day 1 negation exercises", "Hint 3 for Day 1 negation exercises", "Lean at MC 2022", "Introduction", "Pretty Symbols in Lean", "Glossary of Tactics and Lemmas"], "terms": {"todai": [0, 1, 2, 3], "s": [0, 1, 2, 3, 4, 15, 17], "goal": [0, 1, 2, 3, 4, 15, 17], "understand": [0, 1], "philosophi": 0, "theori": [0, 1, 2, 4, 15], "don": [0, 1, 2], "t": [0, 1, 2, 4, 17], "try": [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17], "memor": 0, "anyth": [0, 17], "happen": 0, "automat": 0, "instead": [0, 2, 3, 17], "do": [0, 1, 2, 3, 4, 15], "mani": [0, 14], "exercis": [0, 2, 15], "you": [0, 1, 2, 3, 4, 15, 16, 17], "can": [0, 1, 2, 3, 4, 15, 17], "practic": [0, 1, 4], "onli": [0, 1, 2, 3, 15, 16, 17], "wai": [0, 1, 3, 4, 17], "learn": [0, 2, 15], "new": [0, 1, 2], "program": 0, "languag": 0, "alwai": [0, 1, 2], "save": [0, 1, 2], "your": [0, 1, 2, 4, 8, 12, 13, 16, 17], "work": [0, 1, 2, 4, 17], "The": [0, 2, 4, 14, 15, 16, 17], "easiest": 0, "thi": [0, 1, 2, 3, 4, 15, 17], "browser": 0, "bookmark": 0, "page": [0, 1], "which": [0, 1, 2, 3, 4, 11, 15, 17], "contain": [0, 1, 2, 4], "code": [0, 4, 15], "its": [0, 1, 17], "url": 0, "built": [0, 4, 15], "top": [0, 1, 15], "system": [0, 15], "call": [0, 1, 3, 4, 15], "an": [0, 1, 2, 3, 4, 15, 17], "altern": 0, "set": [0, 1, 2, 3, 15, 17], "In": [0, 1, 2, 3, 4, 15], "element": [0, 1, 4, 15, 17], "we": [0, 1, 2, 3, 4, 15, 17], "have": [0, 1, 2, 4, 14, 17], "term": [0, 1, 2, 3, 4, 12, 15, 17], "everi": [0, 1, 2, 4, 15], "ha": [0, 1, 2, 3, 4, 12, 15, 17], "when": [0, 2, 4, 17], "translat": [0, 17], "math": [0, 1, 2, 4], "either": [0, 1], "mathemat": [0, 1, 4, 15, 17], "object": [0, 15], "function": [0, 4, 15, 16, 17], "proof": [0, 2, 3, 4, 15], "notat": [0, 3, 4], "x": [0, 1, 3, 4, 15, 17], "stand": [0, 1, 3], "inhabit": [0, 1, 4], "For": [0, 1, 2, 3, 4, 17], "most": [0, 2], "think": [0, 1, 4], "ani": [0, 1, 3, 4], "statement": [0, 1, 2, 4], "potenti": 0, "being": [0, 1, 2], "true": [0, 1, 2, 4, 17], "fals": [0, 1, 12, 13, 17], "like": [0, 4, 15, 17], "2": [0, 2, 4, 14, 15, 17], "4": [0, 2, 4, 15, 17], "5": [0, 15], "fermat": 0, "last": 0, "theorem": [0, 1, 2, 3, 4, 15, 17], "riemann": 0, "hypothesi": [0, 1, 2, 3, 4, 17], "special": [0, 1, 15], "prop": [0, 1, 4, 17], "whose": 0, "ar": [0, 1, 2, 4, 12, 15, 17], "furthermor": 0, "each": [0, 4, 15, 17], "p": [0, 1, 2, 3, 4, 17], "itself": [0, 1], "hp": [0, 1, 2, 3, 4, 12, 17], "As": [0, 1, 2], "produc": [0, 16, 17], "same": [0, 1, 2, 15, 17], "so": [0, 1, 2, 4, 15, 17], "exist": [0, 1, 3, 4, 16], "throughout": 0, "note": [0, 1, 2, 4], "q": [0, 1, 2, 4, 8, 12, 13, 17], "r": [0, 1, 17], "denot": 0, "written": [0, 2], "us": [0, 1, 2, 3, 4, 8, 11, 16, 17], "follow": [0, 1, 2, 3, 4, 15, 16], "syntax": 0, "fermats_last_theorem": 0, "n": [0, 1, 2, 4, 15, 17], "\u2115": [0, 1, 2, 3, 4, 15, 16, 17], "n_gt_2": 0, "y": [0, 1, 15, 17], "z": [0, 1, 15], "0": [0, 1, 2, 4, 15, 17], "begin": [0, 1, 2, 3, 4, 15], "sorri": [0, 1, 2, 3, 4, 7, 9, 11, 15], "end": [0, 1, 2, 3, 4, 15, 17], "let": [0, 1, 3, 4, 17], "pars": 0, "abov": [0, 1, 4], "ignor": 0, "multipl": [0, 1, 2, 4], "whitespac": 0, "tab": [0, 16], "line": [0, 1, 2, 4], "could": [0, 17], "theoret": 0, "write": [0, 2, 4, 15], "entir": [0, 4], "singl": [0, 1, 2], "pleas": 0, "name": [0, 3, 4, 15, 17], "two": [0, 2, 4, 12, 14, 15, 17], "hypothes": [0, 2, 12, 17], "former": 0, "sai": [0, 1, 2, 3, 4, 17], "natur": [0, 1, 2, 3, 4, 15, 16, 17], "number": [0, 1, 2, 3, 4, 15, 16, 17], "latter": 0, "delimit": 0, "between": [0, 2], "target": [0, 1, 2, 3, 4, 8, 13, 17], "ll": [0, 2, 3, 4, 15, 17], "all": [0, 1, 3, 15, 16, 17], "symbol": [0, 1, 2, 3, 14, 17], "soon": 0, "start": [0, 1, 2, 3, 4], "open": [0, 1, 2, 3, 4, 15], "up": [0, 1, 2, 3, 17], "window": [0, 2, 15, 17], "keep": [0, 1], "track": [0, 1], "exampl": [0, 1, 2, 3, 4, 17], "command": [0, 4], "tactic": [0, 1, 2, 3, 4, 11, 14, 15, 16], "veri": [0, 1, 2, 3, 15, 16, 17], "import": [0, 1, 2, 4, 17], "must": 0, "comma": 0, "even": [0, 2], "though": 0, "thei": [0, 1, 2], "explicitli": [0, 2], "displai": 0, "librari": [0, 2, 3, 17], "also": [0, 1, 2, 4, 15, 17], "close": [0, 1, 2, 4, 17], "impli": [0, 1, 16, 17], "both": [0, 2], "just": [0, 1, 2, 4, 15], "f": [0, 1, 2, 3, 4, 15, 17], "given": [0, 1, 17], "If": [0, 1, 2, 3, 4, 8, 12, 13, 17], "empti": [0, 1], "from": [0, 1, 2, 3, 4, 11, 15, 17], "henc": 0, "editor": [0, 16], "prove": [0, 1, 2, 4, 15], "section": 0, "tabl": 0, "describ": 0, "what": [0, 1, 2, 3, 17], "doe": [0, 17], "solv": [0, 2], "see": [0, 1, 2, 4, 15, 17], "action": 0, "first": [0, 2, 3, 4, 17], "refin": [0, 1, 2, 13, 17], "rintro": [0, 1, 3, 4, 5, 8, 9, 17], "current": [0, 1, 4, 17], "were": [0, 17], "requir": [0, 1, 2, 3, 17], "chang": [0, 1, 2, 17], "order": [0, 17], "defin": [0, 1, 2, 3, 4, 17], "need": [0, 1, 2, 3, 5, 6, 7, 8, 12, 17], "choos": [0, 2, 17], "introduc": [0, 17], "arbitrari": [0, 4, 17], "want": [0, 1, 3, 4, 17], "repeatedli": [0, 17], "h1": [0, 1, 5, 9, 17], "h2": [0, 1, 5, 9, 17], "delet": [0, 1, 2], "below": [0, 1, 2], "replac": [0, 1, 2, 3, 17], "them": [0, 1, 2], "legitim": [0, 1, 2], "tautolog": [0, 1], "find": [0, 1], "differ": [0, 1, 2, 3, 4, 17], "know": [0, 1, 2, 3, 4], "how": [0, 1, 2, 4], "finish": 0, "about": [0, 1, 2, 4, 15], "partial": 0, "progress": 0, "here": [0, 1, 2, 17], "approach": 0, "One": [0, 4, 15, 17], "forward": 0, "reason": [0, 17], "other": [0, 1, 2, 3, 4, 17], "again": [0, 3], "backward": [0, 17], "case": [0, 1, 2, 3, 4, 5, 7, 9, 11, 17], "send": 0, "liter": [0, 4, 17], "although": [0, 1], "often": [0, 1, 2, 4, 17], "skip": 0, "parenthes": 0, "creat": [0, 1, 3, 4, 14, 15, 17], "intermedi": [0, 17], "variabl": [0, 1, 4, 17], "hq": [0, 1, 2, 3, 8, 17], "_": [0, 13, 17], "equival": [0, 1, 17], "becaus": [0, 1, 3, 17], "suffic": [0, 17], "provid": [0, 1, 2, 3, 4, 15, 17], "later": [0, 1, 2], "interchang": [0, 1], "big": 0, "healthi": 0, "combin": [0, 1, 3, 17], "make": [0, 1, 2, 3, 4, 11], "readabl": [0, 2], "g": [0, 1, 4, 17], "u": [0, 4], "hpq": [0, 17], "hqr": 0, "hqt": 0, "hst": 0, "htu": 0, "lot": [0, 2, 4, 15], "week": 0, "ever": [0, 3, 17], "lose": 0, "check": [0, 1, 2, 15], "out": [0, 2, 4, 16], "glossari": [0, 1, 11, 14], "list": 0, "mention": [0, 1], "well": [0, 17], "some": [0, 1, 3, 4, 15, 17], "class": [0, 14, 15, 17], "mai": [0, 1, 17], "come": 0, "read": [0, 1, 2, 3, 15], "oper": [0, 1, 2, 15, 16, 17], "easi": [0, 1, 3], "vice": 0, "versa": 0, "similarli": [0, 2], "subtl": 0, "topmost": 0, "after": [0, 1], "should": [0, 2, 17], "off": 0, "attempt": [0, 15], "second": [0, 3, 17], "Then": [0, 17], "put": [0, 3], "cursor": 0, "monitor": 0, "right": [0, 1, 2, 3, 15, 17], "one": [0, 1, 2, 3, 4, 13, 15, 17], "time": [0, 1, 2], "gener": [0, 1, 3, 4, 17], "break": [0, 1, 2, 17], "complic": [0, 1, 2, 16, 17], "simpler": [0, 2, 17], "ones": [0, 17], "fg": [0, 17], "actual": [0, 1], "shorthand": 0, "add": [0, 1, 2, 17], "split": [0, 17], "left": [0, 1, 17], "wise": 0, "bracket_exampl": 0, "ve": 0, "discuss": 0, "build": [0, 16], "pretti": [0, 1, 2, 14, 17], "much": [0, 17], "thing": [0, 1, 2, 4, 15, 17], "seen": [0, 1, 2, 3], "howev": [0, 2], "directli": [0, 1], "angl": 0, "langl": [0, 3, 16, 17], "rangl": [0, 3, 16, 17], "pair": 0, "consist": 0, "explor": 0, "rewrit": [0, 1, 4, 17], "Such": 0, "justifi": 0, "definit": [0, 1, 2, 3, 4, 16, 17], "To": [0, 1, 2, 4, 16], "summar": 0, "recal": [0, 1], "hint": [0, 1, 2], "get": [0, 1, 2, 3, 4, 17], "stuck": [0, 1], "self_imp_not_not_self": 0, "contraposit": [0, 17], "now": [0, 2, 4], "re": [0, 1, 2, 4, 17], "talk": [0, 1], "everybodi": 0, "favorit": 0, "least": [0, 1, 2, 15], "techniqu": 0, "contradict": [0, 1, 3], "version": 0, "principl": [0, 4], "explos": 0, "deriv": [0, 3, 17], "fact": [0, 1, 2, 17], "whenev": [0, 2], "elim": [0, 1, 17], "principle_of_explos": [0, 1], "might": [0, 1, 2], "wonder": 0, "cool": 0, "why": [0, 1], "i": [0, 4], "heard": 0, "befor": [0, 1], "highli": [0, 15], "depend": [0, 1], "where": [0, 4, 17], "datatyp": 0, "onc": [0, 1, 4, 15, 17], "comput": [0, 2], "immedi": [0, 3, 4], "manipul": [0, 2, 17], "valid": [0, 3], "accident": 0, "divid": [0, 2], "unfortun": 0, "mean": [0, 1, 3, 15], "\u2124": [0, 4, 16], "subtract": 0, "buddi": 0, "anoth": [0, 3, 4, 15], "issu": 0, "world": [0, 15], "allow": [0, 4], "coerc": [0, 4], "properli": 0, "\u211a": [0, 4], "divis": [0, 14, 16], "few": 0, "drive": 0, "mathematician": [0, 1], "awai": [0, 4, 17], "But": [0, 2, 3, 4], "difficult": 0, "With": 0, "becom": [0, 3], "exact": [0, 1, 17], "equiconsist": 0, "slightli": [0, 2, 3], "stronger": 0, "zfc": 0, "accept": 0, "axiom": [0, 1, 2], "mario": 0, "carneiro": 0, "ms": 0, "thesi": 0, "footnot": [0, 16], "except": 0, "under": [0, 1], "staff": [0, 15], "supervis": 0, "wrap": 1, "remain": 1, "bit": [1, 3, 14], "move": 1, "rememb": [1, 2, 3, 4, 17], "stuff": 1, "did": 1, "yesterdai": [1, 3], "A": [1, 4], "bracket": [1, 3], "It": [1, 2, 3, 15, 17], "uncommon": 1, "compos": 1, "half": 1, "dozen": 1, "realli": [1, 17], "messi": 1, "unwieldi": 1, "drop": 1, "convent": 1, "express": [1, 2, 4, 17], "b": [1, 2, 3, 4, 17], "c": [1, 2, 3, 4], "d": [1, 2, 3], "arrow": 1, "binari": 1, "feel": 1, "weird": 1, "proposit": [1, 2, 3, 14, 15], "huge": 1, "seem": 1, "unnecessari": 1, "someth": [1, 17], "normal": 1, "hide": 1, "type": [1, 2, 3, 12, 14, 15, 16, 17], "hp1": 1, "hp2": 1, "take": [1, 2], "our": [1, 2], "analog": 1, "further": [1, 4], "form": [1, 17], "e": 1, "homotopi": 1, "taken": [1, 15], "cours": [1, 15], "1": [1, 2, 3, 4, 10, 14, 15, 16, 17], "successfulli": 1, "construct": [1, 2, 4], "purpos": [1, 17], "classic": [1, 2, 4], "sens": 1, "word": [1, 2], "codomain": 1, "input": [1, 2, 3], "consid": [1, 2, 3, 4], "hello_world": 1, "hr": [1, 17], "conveni": 1, "lack": 1, "simul": 1, "forget": 1, "content": 1, "fall": 1, "giant": 1, "umbrella": 1, "curri": 1, "howard": 1, "correspond": [1, 2], "speak": 1, "without": [1, 2, 3], "\u03bb": 1, "plai": [1, 15], "basic": [1, 2, 4, 15, 17], "role": 1, "give": 1, "output": 1, "instanc": [1, 4, 17], "addit": [1, 2], "around": [1, 17], "exactli": [1, 2], "three": 1, "not_not_self_imp_self": 1, "contrapositive_convers": 1, "drastic": 1, "There": 1, "extra": 1, "em": [1, 7, 9, 11, 17], "includ": [1, 3, 4], "would": [1, 2, 17], "prefer": 1, "avoid": [1, 17], "noncomput": [1, 2, 4], "open_local": [1, 2, 4], "file": [1, 4], "show": [1, 2, 3, 4], "ok": 1, "more": [1, 2, 3, 4, 5, 6, 7, 8, 12, 17], "streamlin": 1, "process": [1, 15], "deal": [1, 2, 4, 11], "negat": [1, 11, 14, 16], "shorten": [1, 4], "introduct": [1, 14], "those": 1, "foral": [1, 16], "hpy": [1, 17], "similar": [1, 3, 15, 17], "tool": 1, "wit": [1, 17], "extract": 1, "kei": [1, 7, 11, 17], "tri": [1, 2, 4, 17], "final": [1, 14], "enough": [1, 2], "fun": [1, 3, 15], "disprov": 1, "due": 1, "bertrand": 1, "russel": 1, "claim": 1, "certain": 1, "town": 1, "male": 1, "shave": [1, 9], "men": 1, "who": 1, "themselv": 1, "man": 1, "assum": [1, 4], "main": 1, "loung": 1, "non": [1, 2, 3], "At": 1, "fix": 1, "moment": 1, "someon": 1, "everyon": 1, "camper": [1, 15], "math_campers_singing_paradox": 1, "alic": 1, "sure": 1, "relat": [1, 2], "map": 1, "reflex": 1, "symmetr": 1, "transit": 1, "connect": [1, 2], "reflexive_of_symmetric_transitive_and_connect": 1, "h_symm": 1, "h_tran": 1, "h_connect": 1, "far": [1, 2], "hand": [1, 2, 3], "mess": 1, "usual": [1, 2, 3], "rw": [1, 2, 3, 4, 15, 16, 17], "side": [1, 3], "search": [1, 17], "addition": [1, 17], "l": [1, 16], "bunch": 1, "row": 1, "h3": 1, "data": [1, 2, 4], "nat": [1, 2, 3, 4, 16, 17], "variant": [1, 3], "add_self_self_eq_doubl": 1, "two_mul": 1, "problem": [1, 2, 3], "mul_comm": 1, "hyp": 1, "sub_self": 1, "hard": [1, 3], "h": [1, 3, 4, 5, 9, 17], "rid": [1, 4], "unfold": [1, 4, 17], "everywher": 1, "comp_app": 1, "hf": 1, "hg": 1, "hgf": 1, "mathlib": [2, 17], "focu": 2, "go": [2, 15], "lean": [2, 3, 4], "k": [2, 3, 4, 17], "simpli": [2, 3], "warn": 2, "mid": [2, 16], "vertic": 2, "keyboard": [2, 16], "littl": 2, "back": 2, "prime_def_lt": 2, "m": [2, 4, 17], "101": 2, "possibl": [2, 4], "down": [2, 3], "rabbit": 2, "hole": 2, "exhaust": 2, "kind": [2, 15], "rather": 2, "autom": 2, "norm_num": [2, 17], "involv": [2, 17], "arithmet": [2, 17], "power": 2, "assumpt": [2, 3, 13, 17], "simplifi": [2, 15, 17], "ring_nf": [2, 4, 17], "algebra": [2, 17], "linarith": [2, 3, 17], "inequ": [2, 17], "solver": [2, 17], "sometim": [2, 3, 4], "aren": 2, "2020": [2, 15], "long": 2, "done": [2, 4], "origin": 2, "alreadi": [2, 17], "intern": 2, "crucial": 2, "abl": 2, "match": 2, "hn": 2, "hn2": 2, "lemma": [2, 4, 14], "dvd_sub": 2, "infer": [2, 3], "rest": [2, 3], "tomorrow": 2, "dvd_sub_on": 2, "strategi": 2, "greater": [2, 3], "than": [2, 3], "smallest": [2, 3], "factor": [2, 3], "not_dvd_on": 2, "factori": 2, "factorial_po": 2, "dvd_factori": 2, "min_fac": [2, 3], "min_fac_prim": [2, 3], "min_fac_po": 2, "min_fac_dvd": 2, "step": [2, 4], "sketch": 2, "paper": 2, "lost": 2, "exists_infinite_prim": 2, "abbrevi": [2, 3, 17], "great": [2, 15], "wa": 2, "leav": 2, "detail": [2, 15], "realiz": 2, "expect": 2, "reader": 2, "intellig": 2, "fill": [2, 17], "bug": 2, "featur": [2, 15], "On": [2, 15], "too": 2, "obvious": 2, "argument": [2, 14], "undecipher": 2, "wrong": 2, "unlik": 2, "human": 2, "dumb": 2, "tell": 2, "cannot": [2, 4], "humanli": 2, "imposs": [2, 4], "teach": [2, 3, 15], "collect": 2, "comprehens": [2, 15], "scan": 2, "sadli": 2, "harder": 2, "small": 2, "frequent": 2, "goe": 2, "hope": 2, "ai": 2, "eventu": [2, 4], "elimin": 2, "machin": 2, "review": 3, "concept": 3, "encount": [3, 17], "trivial": [3, 4, 14], "prime": [3, 14, 15], "told": 3, "That": 3, "pass": 3, "made": 3, "curli": 3, "while": [3, 4, 15], "hne1": 3, "ambigu": 3, "unabl": 3, "forc": 3, "explicit": 3, "sparingli": 3, "debug": 3, "suppos": 3, "conclud": 3, "10": 3, "appli": [3, 4, 17], "ten_ne_zero": 3, "specifi": 3, "noth": 3, "posit": 3, "crux": 3, "loss": 3, "quit": 3, "effort": 3, "broken": 3, "sever": [3, 4], "part": [3, 14, 17], "gcd": 3, "descript": 3, "comment": 3, "dvd_of_dvd_pow": 3, "challeng": 3, "mode": 3, "even_or_odd": 3, "two_dvd_of_two_dvd_sq": 3, "hk": 3, "division_lemma_n": 3, "hmn": [3, 17], "div_2": 3, "hnm": 3, "division_lemma_m": 3, "not_coprime_of_dvd_of_dvd": 3, "sqrt2_irrat": [3, 4], "h_cop": 3, "iter": [3, 15], "rcase": [3, 17], "pow_po": 3, "ge_zero_sq_ge_zero": 3, "hne": 3, "mul_left_inj": 3, "cancellation_lemma": 3, "hk_po": 3, "gcd_pos_of_pos_left": 3, "gcd_pos_of_pos_right": 3, "exists_coprim": 3, "pos_of_ne_zero": 3, "wlog_coprim": 3, "hm0": 3, "reduc": [3, 4], "clutter": 3, "abil": 4, "group": [4, 15], "nest": 4, "hierarch": 4, "mcsp": 4, "def": [4, 15], "tau": 4, "eval": [4, 15], "error": [4, 16], "declar": 4, "identifi": 4, "full": 4, "prefix": 4, "within": 4, "refer": 4, "shorter": 4, "longer": 4, "bring": 4, "context": 4, "access": 4, "short": 4, "equal": [4, 14, 16], "absolut": 4, "valu": 4, "round": [4, 15], "through": [4, 16], "live": 4, "integ": [4, 16], "inject": 4, "necessari": 4, "norm_cast": 4, "clear": 4, "int": [4, 16], "sqrt2_irrational_nat": 4, "num_2": 4, "num": 4, "denom_2": 4, "denom": 4, "denomin": 4, "numer": 4, "nat_ab": 4, "nat_abs_mul_self": 4, "coe_nat_inj": 4, "rat": 4, "mul_self_denom": 4, "mul_self_num": 4, "denom_ne_zero": 4, "cast_on": 4, "cast_two": 4, "cast_mul": 4, "pow_two": 4, "clear_denom": 4, "eq_iff_mul_eq_mul": 4, "mp": 4, "complex": [4, 15, 17], "structur": 4, "famili": 4, "mark": 4, "particular": [4, 15], "templat": 4, "attribut": 4, "field": 4, "mul": 4, "\u03c0": 4, "\u03b1": 4, "mul_assoc": 4, "c_1": 4, "one_mul": 4, "mul_on": 4, "inv": 4, "mul_left_inv": 4, "\u00b9": 4, "look": 4, "sourc": [4, 15], "gradual": 4, "extend": 4, "has_on": 4, "ident": 4, "has_mul": 4, "has_inv": 4, "invers": 4, "semigroup": 4, "associ": 4, "monoid": 4, "keyword": 4, "vast": 4, "fifti": 4, "group_theori": 4, "order_of_el": 4, "print": 4, "cyclic_group": 4, "has_gener": 4, "zpow_add": 4, "u_1": 4, "add_comm": 4, "add_comm_semigroup": 4, "mul_comm_of_cycl": 4, "hc": 4, "beyond": 4, "familiar": 4, "afunct": 4, "sum_first": 4, "sum": 4, "famou": 4, "formula": 4, "properti": [4, 15, 17], "ih": [4, 17], "base": [4, 15, 17], "succ": [4, 17], "succ_eq_add_on": [4, 17], "refl": [4, 17], "handl": [4, 17], "sum_first_formula": 4, "plenti": 4, "game": [4, 15], "h_le": 6, "bob": [7, 11], "hye": [7, 9, 11], "hno": [7, 9, 11], "h_one": 10, "push_neg": [11, 17], "easier": 11, "hnp": 12, "hnq": [13, 17], "logic": 14, "implic": 14, "And": 14, "Or": 14, "remark": 14, "behind": 14, "scene": 14, "law": [14, 17], "exclud": [14, 17], "middl": [14, 17], "quantifi": [14, 16], "infinit": 14, "calcul": [14, 17], "subgoal": [14, 17], "sqrt": [14, 15], "irrat": 14, "implicit": 14, "piec": [14, 17], "namespac": 14, "coercion": 14, "recurs": 14, "induct": 14, "checker": 15, "assist": 15, "explain": 15, "correct": 15, "formal": 15, "notion": 15, "compar": 15, "interpret": 15, "By": 15, "verifi": 15, "3": 15, "easy_theorem_stat": 15, "fermats_last_theorem_stat": 15, "easy_proof": 15, "easy_theorem": 15, "hard_proof": 15, "cheat": 15, "snippet": 15, "hello": 15, "click": [15, 17], "button": 15, "upper": 15, "corner": 15, "copi": 15, "edit": 15, "feedback": 15, "infoview": 15, "inlin": 15, "recommend": 15, "along": 15, "These": 15, "design": 15, "dai": 15, "crash": 15, "mathcamp": 15, "2022": 15, "increasingli": 15, "infinitud": 15, "irration": 15, "sneak": 15, "peek": 15, "simultan": 15, "option": 15, "addict": 15, "onlin": 15, "book": 15, "aim": 15, "cover": 15, "aspect": 15, "commun": 15, "welcom": 15, "newcom": 15, "peopl": 15, "avail": 15, "zulip": 15, "chat": 15, "clock": 15, "answer": 15, "question": 15, "join": 15, "kevin": 15, "buzzard": 15, "discord": 15, "server": 15, "rel": 15, "younger": 15, "crowd": 15, "develop": 15, "aaron": 15, "anderson": 15, "updat": 15, "apurva": 15, "nakad": 15, "jalex": 15, "stark": 15, "help": 15, "joanna": 15, "maya": 15, "larg": 15, "chunk": 15, "variou": 15, "resourc": 15, "leanprov": 15, "websit": 15, "100": 15, "articl": 15, "video": 15, "blog": 15, "post": 15, "etc": 15, "xena": 15, "project": 15, "mechan": 15, "futur": 15, "twitch": 15, "channel": 15, "checkout": 15, "summer": 15, "shortcut": 16, "space": 16, "unicod": 16, "iff": 16, "circ": 16, "composit": 16, "ne": 16, "simpl": 16, "Be": 16, "care": 16, "cryptic": 16, "summari": 17, "common": 17, "fulli": 17, "somewhat": 17, "miss": 17, "x1": 17, "x2": 17, "x3": 17, "separ": 17, "dispos": 17, "meanwhil": 17, "hx": 17, "accomplish": 17, "hme0": 17, "compon": 17, "Not": 17, "exfalso": 17, "ex": 17, "falso": 17, "quodlibet": 17, "contradictori": 17, "present": 17, "by_cas": 17, "by_contradict": 17, "essenti": 17, "push": 17, "across": 17, "contrapos": 17, "enter": 17, "simp": 17, "behavior": 17, "ad": 17, "doesn": 17, "squeeze_simp": 17, "instruct": 17, "surject": 17}, "objects": {}, "objtypes": {}, "objnames": {}, "titleterms": {"logic": [0, 1], "lean": [0, 1, 14, 15, 16, 17], "part": [0, 1], "1": [0, 5, 6, 7, 8, 12, 13], "proposit": 0, "type": [0, 4], "implic": [0, 17], "And": [0, 17], "Or": [0, 17], "option": [0, 1], "sidenot": [0, 1], "bracket": 0, "negat": [0, 8, 12, 13, 17], "final": [0, 2], "remark": [0, 2], "2": [1, 3, 9, 10, 11, 12], "behind": 1, "scene": 1, "proof": [1, 17], "irrelev": 1, "function": 1, "lambda": 1, "The": [1, 3], "law": 1, "exclud": 1, "middl": 1, "quantifi": [1, 17], "barber": [1, 5, 9], "paradox": [1, 5, 7, 9, 11], "mathcamp": 1, "sing": [1, 7, 11], "relationship": 1, "conundrum": 1, "equal": [1, 17], "surject": 1, "infinit": 2, "mani": 2, "prime": 2, "divis": 2, "trivial": [2, 17], "calcul": 2, "creat": 2, "subgoal": 2, "sqrt": 3, "irrat": 3, "implicit": 3, "argument": 3, "two": 3, "have": [3, 6, 10], "lemma": [3, 17], "prove": [3, 17], "assum": 3, "m": 3, "n": 3, "ar": 3, "coprim": 3, "0": 3, "bit": 4, "piec": 4, "namespac": 4, "coercion": 4, "class": 4, "recurs": 4, "induct": [4, 17], "hint": [5, 6, 7, 8, 9, 10, 11, 12, 13], "exercis": [6, 8, 10, 12, 13], "math": [7, 11], "camper": [7, 11], "dai": [8, 12, 13], "3": 13, "mc": 14, "2022": 14, "introduct": 15, "what": 15, "how": 15, "us": 15, "note": 15, "acknowledg": 15, "link": 15, "pretti": 16, "symbol": 16, "glossari": 17, "tactic": 17, "contradict": 17, "statement": 17}, "envversion": {"sphinx.domains.c": 2, "sphinx.domains.changeset": 1, "sphinx.domains.citation": 1, "sphinx.domains.cpp": 6, "sphinx.domains.index": 1, "sphinx.domains.javascript": 2, "sphinx.domains.math": 2, "sphinx.domains.python": 3, "sphinx.domains.rst": 2, "sphinx.domains.std": 2, "sphinx.ext.todo": 2, "sphinx": 56}})