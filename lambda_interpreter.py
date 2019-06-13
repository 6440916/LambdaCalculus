from lambda_calculus import *


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


if __name__ == "__main__":
    init()
    run()

'''
x0 = Variable(link=0)
x1 = Variable(link=1)
x2 = Variable(link=2)
x3 = Variable(link=3)
x4 = Variable(link=4)
x5 = Variable(link=5)

# Booleans
ID = Abstraction(x0)
TRUE = Abstraction(Abstraction(x1))
FALSE = Abstraction(Abstraction(x0))
NOT = Abstraction(Application(Application(x0, FALSE), TRUE))
OR = Abstraction(Abstraction(Application(Application(x1, TRUE), x0)))
AND = Abstraction(Abstraction(Application(Application(x1, x0), FALSE)))
XOR = Abstraction(Abstraction(Application(Application(x1, Application(NOT, x0)), x0)))
EQ = Abstraction(Abstraction(Application(Application(x1, x0), Application(NOT, x0))))

XOR2 = Abstraction(Abstraction(Application(Application(AND, Application(Application(OR, x0), x1)), Application(NOT, Application(Application(AND, x1), x0)))))

# Integers
ZERO = Abstraction(Abstraction(x0))
SUCC = Abstraction(Abstraction(Abstraction(Application(x1, Application(Application(x2, x1), x0)))))

test = Application(Application(EQ, XOR), XOR2)

last = test
while test != None:
    last = test
    test = test.beta_reduce()
print(last)
'''
