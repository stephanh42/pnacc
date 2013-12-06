"""Please Not Another Compiler Compiler -- LR parser generator library.
"""

from collections import namedtuple
from operator import methodcaller
from functools import partial
import sys
import re

_str_type = globals().get("basestring", str)

def identity(x):
    """Identity functions, useful as semantic action for rules."""
    return x

def namedtuple_with_visit(name, fields, doc=""):
    """Similar to `collections.namedtuple' but in addition has a `visit' method.

    Example:
    Foo = namedtuple_with_visit("Foo", "x y")
    foo = Foo(3, 4)
    class Visitor:
        def Foo(self, x, y): 
            print("Foo(%d,%d) % (x, y))
    foo.visit(Visitor())
    # prints Foo(3,4)
    """
    def visit(self, visitor):
        return getattr(visitor, name)(*self)
    cls = type(name, (namedtuple(name, fields),), {"__slots__" : (), "visit": visit, "__doc__":doc})
    visit.__doc__ = "Calls visitor.%s(%s)" % (name, ", ".join(cls._fields))
    return cls

Shift = namedtuple_with_visit("Shift", "state", "Represents a Shift action.")
Goto = namedtuple_with_visit("Goto", "state", "Represent a Goto action for non-terminals.")
Reduce = namedtuple_with_visit("Reduce", "rule pop nonterminal", "Represent a Reduce action.")
Accept = namedtuple_with_visit("Accept", "", "Means that the parsing is complete and succesfull.")
Conflict = namedtuple_with_visit("Conflict", "actions", "A conflict between two or more parsing actions.")
Error = namedtuple_with_visit("Error", "", "Illegal input.")

class _LR0Item(namedtuple("_LR0Item", "rule position")):
    __slots__ = ()

    def __str__(self):
        rule = self.rule
        id = rule.id
        if id == -1:
            rule_str = "Start rule"
        else:
            rule_str = "Rule %d" % id
        names = rule.rhs_names[:self.position] + ["."] + rule.rhs_names[self.position:]
        return rule_str + " : " + rule.lhs_name + " -> " + " ".join(names)

    def reducable(self):
        return self.rule.N == self.position

    def is_interesting(self):
        return True
        return self.position > 0 or self.rule.id == -1 or self.rule.N == 0


class _LR1Item(namedtuple("_LR1Item", "lr0item lookaheads")):
    __slots__ = ()

    def __str__(self):
        return str(self.lr0item) + "   look-ahead: " + " ".join(lookahead.name for lookahead in self.lookaheads)

    def compute_closure(self, visited, depth=0):
        lr0item = self.lr0item

        visited_lookaheads = visited.get(lr0item, frozenset())
        if visited_lookaheads.issuperset(self.lookaheads):
            return
        visited[lr0item] = visited_lookaheads.union(self.lookaheads)

        rule = lr0item.rule
        position = lr0item.position
        if position < rule.N:
            next_symbol = rule.rhs[position]
            if not next_symbol.is_terminal:
                lookaheads = rule.item_first[position + 1]
                if rule.item_nullable[position + 1]:
                    lookaheads = lookaheads.union(self.lookaheads)
                if lookaheads:
                    for new_lr0item in next_symbol.start_items:
                        new_item = _LR1Item(new_lr0item, lookaheads)
                        new_item.compute_closure(visited, depth+1)


def _itemset_closure(itemset):
    visited = {}
    for item in itemset:
        item.compute_closure(visited)
    return frozenset(_LR1Item(k, visited[k]) for k in visited)

def _itemset_advance(itemset, mapping):
    transition_table = {}
    for item in itemset:
        lr0item = item.lr0item
        rule = lr0item.rule
        position = lr0item.position
        if position < rule.N:
            next_symbol = rule.rhs[position]
            transition_set = transition_table.get(next_symbol, [])
            transition_set.append(_LR1Item(_LR0Item(rule, position + 1), item.lookaheads))
            transition_table[next_symbol] = transition_set

    return {k.name: mapping(k, _itemset_closure(transition_table[k])) for k in transition_table}


def _merge_actions(action1, action2):
    if action1 is None:
        return action2
    elif isinstance(action1, Conflict):
        return Conflict(action1.actions + (action2,))
    else:
        return Conflict((action1, action2))

class _Rule(object):
    nullable = False

    def __init__(self, rule, id):
        self.rule = rule
        self.id = id
        lhs, rhs = rule.split("->", 1)
        self.lhs_name = lhs.strip()
        self.rhs_names = rhs.split()
        N = len(self.rhs_names)
        self.N = N
        self.item_nullable = [False] * N + [True]
        self.item_first = [frozenset()] * (N + 1)

    def __repr__(self):
        return "_Rule(%s, %s)" % (repr(self.rule), self.id)

    def compute_nullable(self):
        rhs = self.rhs
        item_nullable = self.item_nullable
        nullable = True
        for i in range(len(rhs))[::-1]:
            sym = rhs[i]
            nullable = nullable and sym.nullable
            item_nullable[i] = nullable
        return item_nullable[0]

    def compute_first(self):
        rhs = self.rhs
        item_first = self.item_first
        first = set()
        for i in range(len(rhs))[::-1]:
            sym = rhs[i]
            sym_first = sym.first
            if sym.nullable:
                first.update(sym_first)
            else:
                first = set(sym_first)
            item_first[i] = frozenset(sym for sym in first if sym.is_terminal)
        return first


class _NonTerminal(object):
    is_terminal = False
    nullable = False

    def __init__(self, name):
        self.name = name
        self.first = frozenset([self])
        self.rules = []

    def compute_nullable(self):
        result = False
        for rule in self.rules:
            nullable = rule.compute_nullable()
            rule.nullable = nullable
            result = result or nullable
        return result

    def compute_first(self):
        result = set(self.first)
        for rule in self.rules:
            first = rule.compute_first()
            rule.first = first
            result.update(first)
        return result


class _Terminal(object):
    is_terminal = True
    nullable = False
    start_items = frozenset()

    def __init__(self, name):
        self.name = name
        self.first = frozenset([self])

    def compute_first(self):
        return self.first

    def compute_nullable(self):
        return True

_eof = "<eof>"


def _make_parse_table(rules, report=None):
    """Given a sequence of grammar rules, create the action table of the LR(1) machine."""
    symbols = {}
    states = []
    states_sentences = []
    states_dict = {frozenset() : None}
    nonterminals = []
    terminals = []

    def make_nonterminal(name):
        """Create a new non-terminal object."""
        nonterm = _NonTerminal(name)
        nonterminals.append(nonterm)
        return nonterm

    def make_terminal(name):
        """Create a new terminal object."""
        term = _Terminal(name)
        terminals.append(term)
        return term

    def make_state(itemset, symbol=None):
        """Create a new state or return existing."""
        try:
            return states_dict[itemset]
        except KeyError:
            state = len(states)
            states.append(itemset)
            if symbol is None:
                state_sentence = ()
            else:
                state_sentence = states_sentences[current_state] + (symbol,)
            states_sentences.append(state_sentence)
            states_dict[itemset] = state
            return state

    def make_action(symbol, itemset):
        """Create either a shift or a goto action."""
        assert symbol != start_symbol
        state = make_state(itemset, symbol)
        if symbol.is_terminal:
            return Shift(state)
        else:
            return Goto(state)

    def compute_fixpoint(name):
        """Compute a fixpoint function on the non-terminals."""
        compute = methodcaller("compute_" + name)
        changed = True
        while changed:
            changed = False
            for nonterm in nonterminals:
                value = compute(nonterm)
                if value != getattr(nonterm, name):
                    setattr(nonterm, name, value)
                    changed = True

    def lookup_symbol(name, create):
        """Find or create a terminal or non-terminal."""
        try:
            return symbols[name]
        except KeyError:
            result = create(name)
            symbols[name] = result
            return result

    # This terminal denotes the end of the input.
    eof = make_terminal(_eof)

    # Initialize the rule objects
    rules = [_Rule(rules[i], i) for i in range(len(rules))]
    for rule in rules:
        lhs = lookup_symbol(rule.lhs_name, make_nonterminal)
        rule.lhs = lhs

    for rule in rules:
        rule.rhs = [lookup_symbol(s, make_terminal) for s in rule.rhs_names]

    # Create the start rule
    start_name = rules[0].lhs_name
    start_symbol = make_nonterminal(start_name + "'")
    start_rule = _Rule("%s' -> %s" % (start_name, start_name), -1)
    start_rule.lhs = start_symbol
    start_rule.rhs = [lookup_symbol(start_name, make_nonterminal)]
    rules.append(start_rule)

    # Distribute the rules over the non-terminals
    for rule in rules:
        rule.lhs.rules.append(rule)

    # Compute `nullable' and `first' properties on non-terminals
    compute_fixpoint("nullable")
    compute_fixpoint("first")

    # Prepare the LR0-items with the position at the start of the rule, for each non-terminal.
    for nonterm in nonterminals:
        nonterm.start_items = [_LR0Item(rule, 0) for rule in nonterm.rules]

    # The initial state
    start_state = make_state(_itemset_closure([_LR1Item(_LR0Item(start_rule, 0), frozenset([eof]))]))

    # Create all states, and fill action table with shift and goto actions
    parse_table = []
    current_state = 0
    while current_state < len(states):
        itemset = states[current_state]
        parse_table.append(_itemset_advance(itemset, make_action))
        current_state = current_state + 1
    parse_table = parse_table

    # Add the reduce/accept actions
    for state in range(len(states)):
        action_row = parse_table[state]
        for lr1item in states[state]:
            lr0item = lr1item.lr0item
            if lr0item.reducable():
                rule = lr0item.rule
                if rule == start_rule:
                    action = Accept()
                else:
                    action = Reduce(rule.id, rule.N, rule.lhs.name)
                for lookahead in lr1item.lookaheads:
                    current_action = action_row.get(lookahead.name, None)
                    action_row[lookahead.name] = _merge_actions(current_action, action)

    # Generate a report, if requested
    if report is not None:
        write = report.write
        write("Terminals: %s\n" % " ".join(term.name for term in terminals))
        for nonterm in nonterminals:
            write("\nNon-terminal %s: nullable: %s, first: %s\n" % (nonterm.name, nonterm.nullable, " ".join(sym.name for sym in nonterm.first if sym.is_terminal)))
            for rule in nonterm.rules:
                for i in range(max(len(rule.rhs), 1)):
                    item = _LR0Item(rule, i)
                    write("%s: nullable: %s, first: %s\n" % (str(item), rule.item_nullable[i], " ".join(sym.name for sym in rule.item_first[i])))
        for state in range(len(states)):
            write("\nState %d, " % state)
            write("example sentence: %s\n" % " ".join(symbol.name for symbol in states_sentences[state]))
            sorted_items = [item for item in states[state] if item.lr0item.is_interesting()]
            sorted_items.sort(key=lambda item: item.lr0item.rule.id)
            write("LR1 itemset:\n" + "".join("  %s\n" % str(item) for item in sorted_items))
            actions = parse_table[state]
            write("Actions:\n")
            write("".join("  %s : %s\n" % (k, actions[k]) for k in actions))

    return parse_table



class FileCache(object):
    def __init__(self, filename):
        self.filename = filename

    def read_object(self):
        with open(self.filename, "rb") as file:
            import pickle
            return pickle.load(file)

    def write_object(self, obj):
        import os.path
        import tempfile
        import shutil

        # On most reasonable operating systems, a move in the same directory is
        # guaranteed to be atomic.
        # This code tries to take advantge of that by first creating temporary file in
        # the destination directory, and then moving it over the destination filename.
        with tempfile.NamedTemporaryFile(dir=os.path.dirname(self.filename), delete=False) as file:
            import pickle
            pickle.dump(obj, file)
            name = file.name

        shutil.move(name, self.filename)

    def get(self, input, compute):
        cached_value = None
        try:
            cached_value = self.read_object()
        except (IOError, OSError, PickleError):
            pass
        if isinstance(cached_value, tuple) and len(cached_value) == 2 and cached_value[0] == input:
            return cached_value[1]
        result = compute(input)
        try:
            self.write_object((input, result))
        except (IOError, OSError, PickleError):
           pass
        return result


def _make_parse_table_cached(rules, cache):
    if isinstance(cache, _str_type):
        cache = FileCache(cache)

    return cache.get(tuple(rules), _make_parse_table)


def make_parse_table(rules, cache=None, report=None):
    if cache is None or report is not None:
        if isinstance(report, _str_type):
            with open(report, "w") as report_file:
                return _make_parse_table(rules, report_file)
        else:
            return _make_parse_table(rules, report)
    else:
        return _make_parse_table_cached(rules, cache)


class ParseError(Exception):
    def __init__(self, message, state, lookahead, parse_table):
        super(Exception, self).__init__(message)
        self.state = state
        self.lookahead = lookahead
        self.parse_table = parse_table

_StackItem = namedtuple("_StackItem", "state value")

class _ParsingContext(object):
    state = 0
    lookahead = None
    accepted = False
    result = None
    error_action = Error()

    def __init__(self, parse_table, actions):
        self.parse_table = parse_table
        self.actions = actions
        self.stack = []

    def feed(self, token):
        self.lookahead = (token.type, token)
        parse_table = self.parse_table
        error_action = self.error_action

        while self.lookahead is not None and not self.accepted:
            action = parse_table[self.state].get(self.lookahead[0], error_action)
            action.visit(self)

    def Shift(self, state):
        self.stack.append(_StackItem(self.state, self.lookahead[1]))
        self.state = state
        self.lookahead = None
    
    def Reduce(self, rule, pop, nonterminal):
        args = []
        state = self.state
        for i in range(pop):
            state, value = self.stack.pop()
            args.append(value)
        args.reverse()
        value = self.actions[rule](*args)
        self.state = state
        self.stack.append(_StackItem(state, value))
        action = self.parse_table[state].get(nonterminal, self.error_action)
        action.visit(self)

    def Accept(self):
        self.accepted = True
        self.result = self.stack.pop().value

    def Goto(self, state):
        self.state = state

    def Error(self):
        raise ParseError("Parse error: unexpected token %s in state %s" % (self.lookahead[0], self.state), self.state, self.lookahead, self.parse_table)

    def Conflict(self, actions):
        raise ParseError("Ambiguous grammar", self.state, self.lookahead, self.parse_table)


class Parser(namedtuple("Parser", "parse_table actions")):
    __slots__ = ()

    def parse(self, tokens):
        context = _ParsingContext(self.parse_table, self.actions)
        item = (None,)
        for item in tokens:
            context.feed(item)
        if item.type != _eof:
            context.feed(Token(_eof, "", (-1, -1)))
        if context.accepted:
            return context.result
        else:
            raise ParseError("Premature end of input", context.state, context.lookahead, context.parse_table)

    def conflicts(self):
        parse_table = self.parse_table
        for state in range(len(parse_table)):
            row = parse_table[state]
            for symbol in row:
                action = row[symbol]
                if isinstance(action, Conflict):
                    yield (state, symbol, action)

    def has_conflicts(self):
        return any(self.conflicts())


def make_parser(rules_and_actions, cache=None, report=None):
    rules = [p[0] for p in rules_and_actions]
    actions = [p[1] for p in rules_and_actions]
    parse_table = make_parse_table(rules, cache=cache, report=report)
    return Parser(parse_table, actions)


class Token(namedtuple("Token", "type text span")):
    def split(self, n):
        first = self.text[:n]
        second = self.text[n:]
        separation = self.span[0] + len(first)
        return (Token(self.type, first, (self.span[0], separation)), Token(self.type, second, (separation, self.span[1])))

class Lexer(object):
    def __init__(self, regexes, flags=0):
        self.no_match = object()
        regex = "(" * len(regexes) + "".join("%s)|" % p[0] for p in regexes) + "."
        self.regex = re.compile(regex, flags=flags)
        self.types = tuple(p[1] for p in regexes)[::-1]
        self.range = range(len(self.types))[::-1]

    def lex(self, str):
        types = self.types
        r = self.range
        no_match = self.no_match
        for mo in self.regex.finditer(str):
            for i in r:
                g = mo.group(i + 1)
                if g:
                    type = types[i]
                    if type is not None:
                        yield Token(type, g, mo.span())
                    break
            else:
                g = mo.group(0)
                yield Token(g, g, mo.span())

        N = len(str)
        yield Token(_eof, "", (N, N))



def _test():
    Add = namedtuple("Add", "e1 e2")
    Mul = namedtuple("Mul", "e1 e2")
    grammar = [
    ("E -> E + E", lambda e1, _, e2: Add(e1, e2)),
    ("E -> T",  lambda x:x),
    ("T -> T * F", lambda e1, _, e2: Mul(e1, e2)),
    ("T -> F", lambda x:x),
    ("F -> ident", lambda x:x),
    ("F -> ( E )", lambda _, x, __: x)
    ]
    parser = make_parser(grammar, report="grammar.out", cache="grammar.cache")
  
    lexer = Lexer([(r"[a-zA-Z0-9]+", "ident"), (r"\s+", None)])

    line = list(lexer.lex("(X + Y ) * 34"))
    print(line)
    print(list(parser.conflicts()))
    result = parser.parse(line)
    print(result)

if __name__ == "__main__":
    _test()
