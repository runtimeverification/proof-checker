
class CircomFragment():
    def __repr__(self):
        raise NotImplementedError

class Expr(CircomFragment):
    pass

class Stmt(CircomFragment):
    pass

class Signal(Expr):
    def __init__(self, name: str, signal_type: str):
        self.name = name
        assert self.type in ["input", "output", ""]
        self.type = signal_type

    def is_input(self):
        return self.type == "input"

    def is_output(self):
        return self.type == "output"
    
    def declaration(self):
        return (' ').join(['signal', self.type, self.name])
    
    def identifier(self):
        return self.name
    
    def __repr__(self):
        return self.identifier

class Add(Expr):
    def __init__(self, lhs: Expr, rhs: Expr):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return f'({(" "). join([self.lhs.declaration(), "+", self.rhs.__repr__()])})'
    
class Mult(Expr):
    def __init__(self, lhs: Expr, rhs: Expr):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return f'({(" "). join([self.lhs.declaration(), "*", self.rhs.__repr__()])})'

class Assignment(Stmt):
    def __init__(self, lhs: Signal, rhs: Expr):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return (' '). join([self.lhs.declaration(), '<==', self.rhs.__repr__()]) + ';'