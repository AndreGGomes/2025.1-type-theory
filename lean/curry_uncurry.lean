def curry : (α × β → γ) → (α → β → γ) -- curryfies the original function
  | f, a, b => f (a, b)
  --^ explains to lean what to do with each argument received by the curryfied function
  --  in terms of the old one


def uncurry : (α → β → γ) → (α × β → γ) -- uncurrifies the original function
  | f, (a, b) => f a b
  --^explains to lean how to transform the 2 arguments of the new function in the 3 arguments
  -- of the original one, bcause the instructions of what the function should do is defined in the old one

  --the explanation of both is valid for each other, just changing the number of arguments


def sum_curry (a : Int) (b : Int) := a + b


-- playing around to see if it works

#check sum_curry

#eval sum_curry 1 2

#check uncurry sum_curry

#eval uncurry sum_curry (1, 2)

def sum_uncurry (p : Int × Int) : Int :=
  p.fst + p.snd -- this could be also p.1 + p.2

#eval sum_uncurry (1, 2)

#eval curry sum_uncurry 1 2
