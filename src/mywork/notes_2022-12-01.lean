/-

Let's build the factorial function with induction.

-/

def fac_zero := 1

def fac_step(n': nat)(n'_fac: nat) := (n' + 1) * n'_fac

def factorial'(n: nat): nat :=
	nat.rec_on
		n
		1
		-- Construct a proof of the value for the next natural number
		fac_step

#eval factorial' 8

def sum_to_zero := 0
def sum_to_next(n': nat)(n'_sum: nat) := n' + n'_sum + 1

def sum_to(n: nat): nat :=
	nat.rec_on
		n
		0
		sum_to_next

#eval sum_to 10
