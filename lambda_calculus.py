#!/usr/bin/env python3
import re
import sys
"""
Lambda Calculus Interpreter by Ruben de Vries (6440916).
"""

"""TODO:
    1. Finish lazy order reduction.
    2. Clean up code
    3. Optimize code
    4. Add types
"""

class LambdaTerm:
    """Abstract Base Class for lambda terms."""

    def __add__(self, other):
        if not isinstance(other, LambdaTerm):
            raise ValueError("Expected lambda term!")
        if self.is_empty():
            return other
        if other.is_empty():
            return self

        return Application(self, other)

    def __eq__(self, other):
        return isinstance(other, LambdaTerm)

    def __str__(self):
        return self.to_string()

    def __repr__(self):
        raise NotImplementedError

    def is_empty(self):
        return False

    def get_alias(self):
        """Returns corresponding alias to lambda term. If none exists, return
        None."""
        for key, value in aliases:
            if self == value:
                return key

    def deep_add(self, other, depth):
        if not isinstance(other, LambdaTerm):
            raise ValueError("Expected lambda term!")
        if self.is_empty():
            return other

        return Application(self, other)

    def substitute(self, substitute, depth=0):
        """Replaces certain variables with the lambda term 'substitute'."""
        raise NotImplementedError

    def beta_reduce(self, type=2):
        """Returns next reduced form. None is returned in case no further
        reduction is possible."""
        if type == NORMAL:
            return self.normal_reduce()
        if type == APPLICATIVE:
            return self.applicative_reduce()

        return self.lazy_reduce()

    def normal_reduce(self):
        raise NotImplementedError

    def applicative_reduce(self):
        raise NotImplementedError

    def lazy_reduce(self):
        raise NotImplementedError

    def to_string(self, var=[], parens=False, use_aliases=True):
        """Returns string representation of lambda term. Var is list of
        variable names to use and parens determines whether or not to return
        string with parens."""
        raise NotImplementedError


class EmptyTerm(LambdaTerm):
    """Represents an empty lambda term. Mainly used in creating lambda terms
    from string."""

    def __eq__(self, other):
        return other.is_empty()

    def __repr__(self):
        return "Empty"

    def is_empty(self):
        return True

    def substitute(self, substitute, depth=0):
        return self

    def normal_reduce(self):
        return (False, self)

    def applicative_reduce(self):
        return (False, self)

    def lazy_reduce(self):
        return (False, self)

    def to_string(self, var=[], parens=False, use_aliases=True):
        return ""


class Variable(LambdaTerm):
    """Represents a variable.

    Attributes:
        bound : true if bound, false if free variable.
        symbol : string value for free variable.
        pos : represents the distance of the variable to the
            corresponding function.
    """

    def __init__(self, symbol = "", pos = -1):
        # Check for correct arguments.
        if not (isinstance(symbol, str) and isinstance(pos, int)):
            raise ValueError("Expected string and integer as arguments.")
        if symbol != "" and pos > -1:
            raise ValueError("Expected either empty symbol or negative pos.")
        if symbol != "":
            bound = False
        elif pos > -1:
            bound = True
        else:
            raise ValueError("Invalid symbol and pos.")

        self.bound = bound
        self.symbol = symbol
        self.pos = pos

    def __repr__(self):
        if self.symbol == "":
            return "Variable(%s)" % (self.pos)

        return "Variable('%s')" % (self.symbol)

    def __eq__(self, other):
        return (isinstance(other, Variable) and self.symbol == other.symbol
                and self.pos == other.pos)

    def substitute(self, substitute, depth = 0):
        """Replaces self with substitute in case depth == pos.
        Also updates pos since substition comes with beta reduction and
        beta reduction means an abstraction has dissappeared."""

        if self.pos == depth:
            if isinstance(substitute, Variable) and substitute.bound:
                return Variable(pos = substitute.pos + depth)
            return substitute
        elif self.pos > depth:
            return Variable(pos = self.pos - 1)

        return self

    def normal_reduce(self):
        return (False, self) # Variables can no longer be beta reduced.

    def applicative_reduce(self):
        return (False, self) # Variables can no longer be beta reduced.

    def lazy_reduce(self):
        return (False, self) # Variables can no longer be beta reduced.

    def to_string(self, var=[], parens=False, use_aliases=True):
        """Returns string representation of a variable."""
        if self.bound:
            index = len(var) - self.pos - 1
            return var[index]
        else:
            return self.symbol


class Abstraction(LambdaTerm):
    """Represents a lambda term of the form (λx.M).

    Attributes:
        body : lambda term.
    """

    def __init__(self, body):
        if not isinstance(body, LambdaTerm): # Check for correct arguments.
            raise ValueError("Expected lambda term.")

        self.body = body

    def __eq__(self, other):
        return (isinstance(other, Abstraction) and self.body == other.body)

    def __repr__(self):
        return "Abstraction(%s)" % repr((self.body))

    def __call__(self, argument):
        return self.body.substitute(argument)

    def deep_add(self, other, depth):
        """Instead of adding other to self, adds other to self's body. So,
        λx.x + λy.y becomes λx.x λy.y instead of (λx.x)(λy.y)."""
        if self.body.is_empty():
            return Abstraction(other)
        if depth > 0:
            return Abstraction(self.body.deep_add(other, depth - 1))

        return Application(self, other)

    def substitute(self, substitute, depth=0):
        """Substitute variables corresponding with depth."""
        depth += 1
        new_body = self.body.substitute(substitute, depth)

        return Abstraction(new_body)

    def normal_reduce(self):
        """Applies beta reduction. Returns true or false depending if
        changes were made."""
        success, new_body = self.body.normal_reduce()
        if success:
            self.body = new_body
            return (True, self)

        return (False, self)

    def applicative_reduce(self):
        """Applies beta reduction. Returns true or false depending if
        changes were made."""
        success, new_body = self.body.applicative_reduce()
        if success:
            self.body = new_body
            return (True, self)

        return (False, self)

    def lazy_reduce(self):
        """Applies beta reduction. Returns true or false depending if
        changes were made."""
        success, new_body = self.body.lazy_reduce()
        if success:
            self.body = new_body
            return (True, self)

        return (False, self)

    def to_string(self, var=[], parens=False, use_aliases=True, curried=False):
        """Returns string representation of lambda abstraction.
        E.g.: λ x0 x1.x0 """
        alias = self.get_alias()
        if alias:
            return alias

        symbol = ("x%d") % (len(var)) # Creates new variable name.
        x = Variable(symbol)
        first = x if curried else "%s%s" % (LAMBDA, x)

        # Check if body is lambda abstraction.
        if isinstance(self.body, Abstraction):
            second =  " %s" % (self.body.to_string(var + [x], False,
                                                   use_aliases, curried=True))
        else:
            second = ".%s" % (self.body.to_string(var + [x], False, use_aliases))

        if parens:
            return "(%s%s)" % (first, second)
        else:
            return "%s%s" % (first, second)


class Application(LambdaTerm):
    """Represents a lambda term of the form (M N).

    Attributes:
        function : a lambda term.
        argument : a lambda term.
    """

    def __init__(self, function, argument):
        if not (isinstance(function, LambdaTerm)
            and isinstance(argument, LambdaTerm)):
            raise ValueError("Expected lambda term.")

        self.function = function
        self.argument = argument

    def __eq__(self, other):
        return (isinstance(other, Application) and
                self.function == other.function and
                self.argument == other.argument)

    def __repr__(self):
        return "Application(%s,%s)" % (repr(self.function), repr(self.argument))

    def deep_add(self, other, depth):
        if self.function.is_empty():
            return Application(other, self.argument)
        if self.argument.is_empty():
            return Application(self.function, other)
        if depth > 0:
            return Application(self.function, self.argument.deep_add(other, depth - 1))

        return Application(self, other)

    def substitute(self, substitute, depth=0):
        """Substitute variables corresponding with depth."""
        new_function = self.function.substitute(substitute, depth)
        new_argument = self.argument.substitute(substitute, depth)

        return Application(new_function, new_argument)

    def normal_reduce(self):
        """Applies normal order reduction. Returns true or false depending if
        changes were made."""
        # First try applying function to argument
        if isinstance(self.function, Abstraction):
            return (True, self.function(self.argument))

        # Second try reducing the function
        if isinstance(self.function, Application):
            success, reduction = self.function.lazy_reduce()
            if success:
                self.function = reduction
                return (True, self)

        # Third try reducing the function
        if (isinstance(self.argument, Application)
            or isinstance(self.argument, Abstraction)):
            success, reduction = self.argument.lazy_reduce()
            if success:
                self.argument = reduction
                return (True, self)

        return (False, self)

    def applicative_reduce(self):
        """Applies applicative order reduction. Returns true or false depending if
        changes were made."""
        # First try reducing the function
        if isinstance(self.function, Application):
            success, reduction = self.function.applicative_reduce()
            if success:
                return (True, Application(reduction, self.argument))

        # Second try reducing the argument
        if (isinstance(self.argument, Application)
            or isinstance(self.argument, Abstraction)):
            success, reduction = self.argument.applicative_reduce()
            if success:
                self.argument = reduction
                return (True, self)

        # Third try applying function to argument
        if isinstance(self.function, Abstraction):
            return (True, self.function(self.argument))

        return (False, self)

    def lazy_reduce(self):
        """Applies lazy order reduction. Returns true or false depending if
        changes were made. Currently, lazy order reduction works exactly
        the same as normal order."""
        # First try applying function to argument
        if isinstance(self.function, Abstraction):
            return (True, self.function(self.argument))

        # Second try reducing the function
        if isinstance(self.function, Application):
            success, reduction = self.function.lazy_reduce()
            if success:
                self.function = reduction
                return (True, self)

        # Third try reducing the function
        if (isinstance(self.argument, Application)
            or isinstance(self.argument, Abstraction)):
            success, reduction = self.argument.lazy_reduce()
            if success:
                self.argument = reduction
                return (True, self)

        return (False, self)

    def to_string(self, var=[], parens=False, use_aliases=True):
        """Returns string representation of lambda term."""
        alias = self.get_alias()
        if alias:
            return alias

        # First checks if parens are needed around str(self.funciton).
        if isinstance(self.function, Abstraction):
            s1 = self.function.to_string(var, True, use_aliases)
        else:
            s1 = self.function.to_string(var, False, use_aliases)

        # Second, checks if parens are needed around str(self.argument).
        if (isinstance(self.argument, Abstraction) or
            isinstance(self.argument, Application)):
            s2 = self.argument.to_string(var, True, use_aliases)
        else:
            s2 = self.argument.to_string(var, False, use_aliases)

        # Finally returns string representation.
        if parens:
            return "(%s %s)" % (s1, s2)
        else:
            return "%s %s" % (s1, s2)


class Lexer():
    """Generic lexer. Maps string to list of tokens defined by a list of
    expressions.

    Attributes:
        expressions : list of tuples.
    """
    def __init__(self, expressions):
        self.expressions = expressions

    def __call__(self, chars):
        pos = 0
        tokens = []
        while pos < len(chars):
            for key, value in self.expressions:
                regex = re.compile(key)
                match = regex.match(chars, pos)
                if match:
                    text = match.group(0) # The matching string
                    pos = match.end(0) # The last index of the match
                    if value == True:
                        tokens.append(text)
                    elif value != False:
                        tokens.append(value)
                    break
            else:
                return False, "ERROR: forbidden character '%s' found!" % (chars[pos])

        return True, tokens


class Parser():
    """Lambda calculus parser."""

    def __init__(self, chars):
        self.chars = chars

    def __call__(self):
        """If possible, translates self.chars to an abstract lambda term
        structure. Returns True and the structure if succeeded. Else returns
        False and the error message."""
        flag, tokens = LAMBDA_LEXER(self.chars)
        if not flag:
            return False, tokens

        flag, error = Parser.check_syntax(tokens)
        if not flag:
            return False, error

        tokens = Parser.format_tokens(tokens)
        return True, Parser.get_term_structure(tokens)

    @staticmethod
    def get_term_structure(tokens):
        # Create lambda term structure from tokens
        pos = 0
        parens = 0 # Position of opening parenthesis
        depth = 0 # How many expressions deep the result has to be appended

        while len(tokens) > 1:
            if pos == len(tokens) or tokens[pos] == ")":
                pos2 = parens
                result = EMPTY_TERM

                while pos2 < pos:
                    if tokens[pos2] == "\\":
                        result = result.deep_add(Abstraction(EMPTY_TERM), depth)
                        depth += 1
                    elif isinstance(tokens[pos2], LambdaTerm):
                        result = result.deep_add(tokens[pos2], depth)
                    elif isinstance(tokens[pos2], int):
                        result =result.deep_add(Variable(pos = tokens[pos2]), depth)
                    elif tokens[pos2] != "(":
                        result = result.deep_add(Variable(symbol = tokens[pos2]), depth)
                    pos2 += 1

                # Restart from beginning
                del tokens[parens:pos + 1]
                tokens.insert(parens, result)
                parens = 0
                pos = 0
                depth = 0
                continue

            if tokens[pos] == "(":
                parens = pos

            pos += 1

        if len(tokens) > 0 :
            return tokens[0]
        else:
            return EMPTY_TERM

    @staticmethod
    def format_tokens(tokens):
        """Formats tokens such that all variables are replaced with integers
        corresponding to the abstraction they are linked with."""

        ABSTRACTION = 0
        APPLICATION = 1
        var = [] # Variable names
        #
        parens = []
        pos = 0
        in_argument = False # Is true if token is surrounded by \ en .

        while pos < len(tokens):
            if tokens[pos] == "(":
                if tokens[pos + 1] == "\\":
                    parens.append(ABSTRACTION)
                else:
                    parens.append(APPLICATION)
            elif tokens[pos] == ")":
                if parens.pop() == ABSTRACTION:
                    var.pop()
            elif tokens[pos] == "\\":
                in_argument = True
                del tokens[pos]
                continue
            elif tokens[pos] == ".":
                in_argument = False
                del tokens[pos]
                continue
            else:
                if in_argument:
                    var.append(tokens[pos])
                    tokens[pos] = "\\"
                else:
                    for i in range(len(var) - 1, -1, -1):
                        if var[i] == tokens[pos]:
                            tokens[pos] = len(var) - i - 1
                            break
            pos += 1

        return tokens

    @staticmethod
    def check_parens(tokens):
        """Check if tokens use parenthesis correctly. That is,
        each opening parenthesis has an associated closing parenthesis."""
        parens = 0 # keeps track of opening and closing parenthesis
        for token in tokens:
            if token == '(':
                parens += 1
            elif token == ')':
                parens -= 1

            if parens < 0:
                return False, "ERROR: closing parenthesis with no opening found!"

        if parens == 0:
            return True, ""

        return False, "ERROR: not every opening parenthesis has a closing one,\
                        or vice versa."

    @staticmethod
    def check_variables(tokens):
        """Check if tokens has no variables of the form xi where i is
        any number."""
        regex = re.compile(r"x[0-9]+$")
        for token in tokens:
            if isinstance(token, str) and regex.match(token):
                return False, "ERROR: forbidden variable '%s' found!" % (token)

        return True, ""

    @staticmethod
    def check_syntax(tokens):
        """Checks if self.chars has correct syntax."""
        flag, error = Parser.check_parens(tokens)
        if flag:
            flag, error = Parser.check_variables(tokens)

        return flag, error


def from_string(string):
    """Creates lambda term from string."""
    parser = Parser(string)
    return parser()

# Some constants
EMPTY_TERM = EmptyTerm()
NORMAL = 0
APPLICATIVE = 1
LAZY = 2
RED = "\033[1;31;47m" # Colours text red with black background
LAMBDA = "\u03BB"

x0 = Variable(pos=0)
x1 = Variable(pos=1)
x2 = Variable(pos=2)
x3 = Variable(pos=3)
x4 = Variable(pos=4)
x5 = Variable(pos=5)

# Booleans
ID = Abstraction(x0)
TRUE = Abstraction(Abstraction(x1))
FALSE = Abstraction(Abstraction(x0))
NOT = Abstraction(Application(Application(x0, FALSE), TRUE))
OR = Abstraction(Abstraction(Application(Application(x1, TRUE), x0)))
AND = Abstraction(Abstraction(Application(Application(x1, x0), FALSE)))
XOR = Abstraction(Abstraction(Application(Application(x1, Application(NOT, x0)), x0)))
EQ = Abstraction(Abstraction(Application(Application(x1, x0), Application(NOT, x0))))

# Integers
ZERO = Abstraction(Abstraction(x0))
SUCC = Abstraction(Abstraction(Abstraction(Application(x1, Application(Application(x2, x1), x0)))))

aliases = [("True", TRUE), ("False", FALSE), ("not", NOT), ("or", OR),
           ("and", AND), ("xor",  XOR), ("equals", EQ), ("id", ID)]

# Lambda calculus token expressions
LAMBDA_EXPS = [
        (r"[ \n\t]+", False),
        (r"\\", True),
        (r"\.", True),
        (r"\(", True),
        (r"\)", True)]
LAMBDA_EXPS.extend(aliases + [(r"[A-Za-z]+[A-Za-z0-9]*", True)])

LAMBDA_LEXER = Lexer(LAMBDA_EXPS)

# =============================================================================
# Lambda Calculus Interpreter
# =============================================================================

if __name__ == "__main__":
    # Beta reduces file if file path is given in arguments
    if len(sys.argv) > 1:
        with open(sys.argv[1]) as file:
            content = file.read()
        success, terms = from_string(content)
        while success:
            success, terms = terms.beta_reduce()
        print(terms)
        sys.exit(0)

    class Command():
        """Simple command object. For example, typing 'close' in terminal will
        close this program.

        Attributes:
            name : the actual name the command is called by.
            description : a description of the command which shows up when using
                the 'help' command.
            function : the function called when the command is executed.
        """

        def __init__(self, name, description, function):
            self.name = name
            self.description = description
            self.function = function

        def __call__(self):
            """Executes command."""
            return self.function()


    def init():
        """Initialize interpreter."""
        print("Lambda calculus interpreter by Ruben de Vries(6440916).")
        print("Type 'help' to find out how it works!")


    def run():
        """Run interpeter."""
        global running, last
        running = True

        while running:
            s = input("> ")

            # Check if input corresponds with existing command
            command_input = False
            for command in COMMANDS:
                if s == command.name:
                    command()
                    command_input = True
                    break
            if command_input:
                continue

            # Translating input to lambda term and reducing it to simplest form
            s = s.replace("last", "(" + last + ")")
            tag, lambda_term = from_string(s)
            while lambda_term != None:
                last = str(lambda_term)
                print(last)
                lambda_term = lambda_term.beta_reduce()


    def command_info():
        """Reveal all commands and their function."""
        print("")
        for command in COMMANDS:
            print(command.description)


    def close():
        """Closes interpreter."""
        print("\nClosing program ...")
        global running
        running = False


    last = ""
    running = False
    COMMANDS = [
            Command("help", "help : reveals all commands and their function.",
                    command_info),
            Command("close", "close : close interpreter.", close)]


    init()
    run()
