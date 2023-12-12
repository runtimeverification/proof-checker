from proof_generation.regex.regex import Regex, Kleene, Choice, Concat, implies, Letter, a, b, EmptySet, Epsilon, Not, less_than
from proof_generation.regex.brzozowski import derivative, brzozowski

even = Kleene(Choice(Concat(a, a), Choice(Concat(a, b), Choice(Concat(b, a), Concat(b, b)))))
odd = Concat(Choice(a, b), even)
top = Kleene(Choice(a, b))

def test_derivative() -> None:
    assert odd == derivative(a, even)

def test_brzozowski() -> None:
    assert brzozowski(a) == False
    assert brzozowski(b) == False
    assert brzozowski(Choice(a, b)) == False
    assert brzozowski(top) == True
    assert brzozowski(implies(Kleene(Kleene(a)), Kleene(a))) == True
    assert brzozowski(implies(Kleene(Kleene(a)), Kleene(Kleene(a)))) == True
    assert brzozowski(implies(Kleene(Concat(a, a)), Choice(Concat(Kleene(a), a), Epsilon()))) == True
    assert brzozowski(Choice(Kleene(Concat(Kleene(a), b)), Kleene(Concat(Kleene(b), a)))) == True
    assert brzozowski(even) == False
    assert brzozowski(Choice(even, odd)) == True
    assert brzozowski(Choice(Not(Concat(top, Concat(a, top))), Not(Kleene(b))))

