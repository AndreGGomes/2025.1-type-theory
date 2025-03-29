#eval 2+5
#eval 1+2*5

#eval (2-44 : Int)

#check 2 + 3 * 2 + 5

#eval String.append "Hello, " "Lean!"

#eval if (2 < 4) then "hi" else "bye"

#check String.append "is is "

def hello := "Oi "

#check hello

#eval String.append hello "mundo"

def g (n : Nat) (m : Nat) := n + m + 2

#eval g 1 2


structure Point where --defining a structure
  x : Float
  y : Float
--deriving Repr

def pt : Point := {x := 2.5 , y := 2.5}

def origin : Point := { x := 0.0, y := 0.0}

def notorigin : Point := { x := 3.4, y := 5.6}

#eval origin

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

#eval addPoints origin notorigin

#check (Point.mk)  --checks the constructor itself
