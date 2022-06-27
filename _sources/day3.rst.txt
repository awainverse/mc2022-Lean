.. _day3:

***********************
Infinitely Many Primes
***********************

Today we will prove that there are infinitely many primes using `mathlib library <https://leanprover-community.github.io/mathlib_docs/>`__. Our focus will be on how to *use* the library to prove more complicated theorems. Remember to always **save your work**.
First, we're going to need to learn how Lean deals with divisibility of natural numbers.

Divisibility and Primes
===================
In mathlib, divisibility for natural numbers is defined as the following *proposition*.

.. code:: 

  a ∣ b := (∃ k : ℕ, a = b * k)

For example, ``2 | 4`` will be a proposition ``∃ k : ℕ, 4 = 2 * k``. 
**Very important.** The statement ``2 | 4`` is not saying that "2 divides 4 *is true*". 
It is simply a proposition that requires a proof. 
**Warning:** If you need to type the divisibility symbol, type ``\mid``. 
This is **not** the vertical line on your keyboard.

Similarly, the mathlib library also contains a definition of ``prime``.
It's a little complicated, but the library has this theorem connecting it back to the definition you know:

.. code:: 

    theorem nat.prime_def_lt'' {p : ℕ} :
      nat.prime p ↔
        2 ≤ p                                     -- p is at least 2
        ∧                                         -- and
        ∀ {m : ℕ}, m ∣ p, m = 1 ∨ m = p           -- if m divides p, then m = 1 or m = p.


Same as with divisibility, for every natural number ``n``, 
``nat.prime n`` is a *proposition*.
So that ``nat.prime 101`` requires a proof.
It is possible to go down the rabbit hole and prove it using just the axioms of natural numbers.
However, this is exhausting work, and exactly the kind of thing we'd rather the computer do!

Trivial calculations
===================
Here are two of Lean's many tactics that automate basic calculations for us.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``norm_num``
    - ``norm_num`` is Lean’s calculator. If the target has a proof that involves *only* numbers and arithmetic operations,
      then ``norm_num`` will close this goal.

      If ``hp : P`` is an assumption then ``norm_num at hp,`` tries to use simplify ``hp`` using basic arithmetic operations.

  * - ``ring_nf`` 
    - ``ring_nf,`` is Lean's algebraic manipulator. 
      If the target has a proof that involves *only* algebraic operations, 
      then ``ring_nf,`` will close the goal.

      If ``hp : P`` is an assumption then ``ring_nf at hp,`` tries to use simplify ``hp`` using basic algebraic operations.

  * - ``linarith`` 
    - ``linarith,`` is Lean's inequality solver.
  
.. code:: lean 

  import tactic data.nat.prime 

  /--------------------------------------------------------------------------

  ``norm_num``

    Useful for arithmetic.
  
  ``ring_nf``

    Useful for basic algebra.

  ``linarith``

    Useful for inequalities.
    

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/
  
  example : 1 > 0 :=
  begin
    sorry,
  end

  example : 101 ∣ 2020 :=
  begin
    sorry,
  end

  example : nat.prime 101 := 
  begin 
    sorry,
  end

  example (m a b : ℕ) :  m^2 + (a + b) * m + a * b = (m + a) * (m + b) :=
  begin
    sorry,
  end

  example (a b c : ℕ) : a < b → b ≤ c → a < c :=
  begin
    sorry,
  end

  example (m a b : ℕ) :  m + a ∣ m^2 + (a + b) * m + a * b :=
  begin
    sorry,
  end

  -- try ``rw nat.prime_def_lt'' at hp,`` to get started
  example (p : ℕ) (hp : nat.prime p) : ¬ (p = 1) :=
  begin 
    sorry,
  end

  example (a b : ℕ) : ¬ a ≤ b → b < a :=
  begin
    sorry,
  end


Creating subgoals
===================
Often when we write a long proof in math, we break it up into simpler problems.
This is done in Lean using the ``have`` tactic. 

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``have``
    - ``have hp : P,`` creates a new goal with target ``P`` and 
      adds ``hp : P`` as a hypothesis to the original goal.

The use of ``have`` that we have already seen is related to this one. 
When you use the tactic ``have hq := f(hp),``
Lean is internally replacing it with ``have hq : Q, exact f(hp),``.

``have`` is crucial for being able to use theorems from the library.
To use these theorems you have to create terms that match the hypothesis *exactly*.
Consider the following example. 
The type ``n > 0`` is not the same as ``0 < n``.
If you need a term of type ``n > 0`` and you only have ``hn : 0 < n``, then you can use
``have hn2 : n > 0, linarith,`` and you will have constructed a term ``hn2`` of type ``n > 0``.


We will need the following lemma later. Remember to save your proof. 
(Here's a :doc:`hint <../hint_1_have_exercise>` if you need one.)

.. code:: lean 

  import tactic data.nat.prime
  open nat

  /--------------------------------------------------------------------------

  ``have``

    ``have hp : P,`` creates a new goal with target ``P`` and 
    adds ``hp : P`` as a hypothesis to the original goal.

  You'll need the following theorem from the library:

  nat.dvd_sub : n ≤ m → k ∣ m → k ∣ n → k ∣ m - n
  
     (Note that you don't need to provide n m k as inputs to dvd_sub
     Lean can infer these from the rest of the expression.
     More on this tomorrow.)

  Delete the ``sorry,`` below and replace it with a legitimate proof.

  --------------------------------------------------------------------------/

  theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → p = 1 :=
  begin
    sorry,
  end


Infinitely many primes 
=======================

We'll now prove that there are infinitely many primes. 
The strategy is to show that there is a prime greater than ``n``, for every natural number ``n``.
We will choose this prime to be smallest non-trivial factor of ``n! + 1``. 
We'll need the following definitions and theorems from the library.

**Primes** 
  * ``m ∣ n := ∃ k : ℕ, m = n * k``
  * ``m.prime :=  2 ≤ p ∧ (∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p)``
  * ``prime.not_dvd_one : (prime p) → ¬ p ∣ 1``

**Factorials**
  * ``n.fact := n!  --n factorial``
  * ``fact_pos : ∀ (n : ℕ), 0 < n.fact``
  * ``dvd_fact : 0 < m → m ≤ n → m ∣ n.fact``

**Smallest factor** 
  * ``n.min_fac :=`` smallest non-trivial factor of ``n``
  * ``min_fac_prime : n ≠ 1 → n.min_fac.prime`` 
  * ``min_fac_pos : ∀ (n : ℕ), 0 < n.min_fac``
  * ``min_fac_dvd : ∀ (n : ℕ), n.min_fac ∣ n``

Check out `data.nat.prime <https://leanprover-community.github.io/mathlib_docs/data/nat/prime.html>`__ for more theorems about primes.
The exercise below is very open-ended.
You should take your time, check the goal window at every step, and sketch out the proof on paper whenever you get lost.

.. code:: lean 

  import tactic data.nat.prime
  noncomputable theory
  open_locale classical

  open nat

  theorem dvd_sub_one {p a : ℕ} : (p ∣ a) → (p ∣ a + 1) → p = 1 :=
  begin
    sorry,
  end

  /-
  dvd_sub_one : (p ∣ a) → (p ∣ a + 1) → p = 1

  m ∣ n := ∃ k : ℕ, m = n * k
  m.prime :=  2 ≤ p ∧ (∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p)
  nat.not_prime_one : ¬ nat.prime 1
  nat.prime.pos : ∀ {p : ℕ}, nat.prime p → 0 < n.min_fac

  n.fact := n! (n factorial)
  fact_pos : ∀ (n : ℕ), 0 < n.fact
  dvd_fact : 0 < m → m ≤ n → m ∣ n.fact

  n.min_fac := smallest non-trivial factor of n
  min_fac_prime : n ≠ 1 → n.min_fac.prime
  min_fac_pos : ∀ (n : ℕ), 0 < n.min_fac
  min_fac_dvd : ∀ (n : ℕ), n.min_fac ∣ n
  -/

  theorem exists_infinite_primes (n : ℕ) : ∃ p, nat.prime p ∧ p ≥ n :=
  begin
    set p:= (n.fact + 1).min_fac,
    sorry,
  end


Final remarks 
=================
It would be great if there was a one-to-one correspondence between "hand-written proofs" and proofs in Lean. But that is far from the case. When we write proofs we leave out a lot of details without even realizing it and expect the reader to be intelligent enough to fill them in. This is both a bug and feature. On the one hand this makes proofs readable. On the other hand too many "obviously true" arguments make proofs undecipherable and often wrong.

Unlike human readers, computers are pretty dumb (as of writing these notes). They can only do what you tell them to do and you cannot expect them to "fill in the details". But it is humanly impossible to teach a computer every single trivial fact about, say the natural numbers. The `Lean math library <https://leanprover-community.github.io/mathlib_docs/>`__ contains a lot of trivial theorems but this collection is far from comprehensive.
So theorem proving is Lean often involves the following steps:

* Scan the library to see which definitions and theorems might be useful.

* Choose the right hypotheses and wording for your theorem to match the theorems in the library. (Sadly, changing the wording slightly might end up making the proof infinitely harder to prove.)

* Break the theorem into small lemmas so that you can use the simplifiers more frequently.

As time goes on, we hope that theorem proving AIs can do more and more of this work and eventually eliminate the difference between human proofs and machine proofs.