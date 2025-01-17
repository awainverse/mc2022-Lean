.. _day4:

**************************
Sqrt 2 is irrational
**************************


Today we will teach Lean that :math:`\sqrt{2}` is irrational.
Let us start by reviewing some concepts we encountered yesterday.

Implicit arguments
====================
Consider the following theorem which says that the smallest non-trivial factor of a natural number greater than 1 is a prime number. 

.. code:: 
  
  min_fac_prime : n ≠ 1 → n.min_fac.prime

It needs only one argument, namely a term of type ``n ≠ 1``.
But we have not told Lean what ``n`` is! 
That's because if we pass a term, say ``hp : 2 ≠ 1`` to ``min_fac_prime`` then from ``hp`` Lean can infer that ``n = 2``.
``n`` is called an *implicit* argument. 
An argument is made implicit by using curly brackets ``{`` and ``}`` instead of the usual ``(`` and ``)`` while defining the theorem.

.. code:: 
  
  theorem min_fac_prime {n : ℕ} (hne1 : n ≠ 1) : n.min_fac.prime := ...

Sometimes the notation is ambiguous and Lean is unable to infer the implicit arguments.
In such a case, you can force all the arguments to become explicit by putting an ``@`` symbol in from on the theorem. For example,

.. code:: 
  
  @min_fac_prime : (n : ℕ) → n ≠ 1 → n.min_fac.prime

Use this sparingly as this makes the proof very hard to read and debug.


The two haves 
===============

We have seen two slightly different variants of the ``have`` tactic. 

.. code:: 

  have hq := ... 
  have hq : ...

In the first case, we are defining ``hq`` to be the term on the right hand side. 
In the second case, we are saying that we do not know what the term ``hq`` is but we know it's type.

Let's consider the example of ``min_fac_prime`` again. 
Suppose we want to conclude that the smallest factor of 10 is a prime. 
We will need a term of type ``10.min_fac.prime``.
If this is the target, we can use ``apply min_fac_prime,``.
If not, we need a proof of ``10 ≠ 1`` to provide as input to ``min_fac_prime``. 
For this we'll use 

.. code::
  
  have ten_ne_zero : 10 ≠ 1,

which will open up a goal with target ``10 ≠ 1``.
If on the other hand, you have another hypothesis, say ``f : P →  (10 ≠ 1)`` and a term ``hp : P``, then 

.. code::
  
  have ten_ne_zero := f(hp)

will immediately create a term of type ``10 ≠ 1``. More generally, remember that 

1. "``:=``" stands for definition. ``x := ...`` means that ``x`` is defined to be the right hand side.
2. "``:``" is a way of specifying type. ``x : ...`` means that the type of ``x`` is the right hand side. 
3. "``=``" is only ever used in propositions and has nothing to do with terms or types.


Sqrt(2) is irrational
=======================
We will show that there do not exist positive natural numbers ``m`` and ``n`` such that 

.. code:: 

  2 * m ^ 2 = n ^ 2  -- (*)

The crux of the proof is very easy. 
You simply have to start with the assumption that ``m`` and ``n`` are coprime *without any loss of generality* and derive a contradiction.
But proving that *without a loss of generality* is a valid argument requires quite a bit of effort. 
This proof is broken down into several parts. 
The first two parts prove ``(*)`` assuming that ``m`` and ``n`` are coprime.
The rest of the parts prove the *without loss of generality* part.

For this problem you'll need the following definitions.

  * ``m.gcd n : ℕ`` is the gcd of ``m`` and ``n``.
  * ``m.coprime n`` is defined to be the proposition ``m.gcd n = 1``.

The descriptions of the library theorems that you'll be needing are included as comments. 
Have fun!

Lemmas for proving (*) assuming m and n are coprime.
------------------------------------------------------------------------------
.. code:: lean
  :name: coprime_lemmas

  import tactic
  import data.nat.basic
  import data.nat.parity


  noncomputable theory
  open_locale classical

  open nat 

  --BEGIN--
  /-
  nat.prime.dvd_of_dvd_pow : ∀ {p m n : ℕ}, p.prime → p ∣ m ^ n → p ∣ m

  Challenge mode: start with nat.even_or_odd instead
  -/
  lemma two_dvd_of_two_dvd_sq {k : ℕ} (hk : 2 ∣ k^2) :
    2 ∣ k :=
  begin
    sorry,
  end

  lemma division_lemma_n {m n : ℕ} 
    (hmn : 2 * m ^ 2 = n ^ 2) 
  : 2 ∣ n :=
  begin
    sorry,
  end

  lemma div_2 {m n : ℕ} (hnm : 2 * m = 2 * n) : (m = n) :=
  begin 
    linarith,
  end 

  lemma division_lemma_m {m n : ℕ} 
    (hmn : 2 * m ^ 2 = n ^ 2) 
  : 2 ∣ m :=
  begin
    sorry,
  end
  --END--

Prove (*) assuming m and n are coprime.
------------------------------------------------------------------------------

.. code:: lean 
  :name: assume_coprime

  import tactic
  import data.nat.basic
  import data.nat.prime


  noncomputable theory
  open_locale classical

  open nat 
  
  lemma two_dvd_of_two_dvd_sq {k : ℕ} 
    (hk : 2 ∣ k ^ 2) 
  : 2 ∣ k :=
  begin
    sorry,
  end

  lemma division_lemma_n {m n : ℕ} 
    (hmn : 2 * m ^ 2 = n ^ 2) 
  : 2 ∣ n :=
  begin
    sorry,
  end

  lemma division_lemma_m {m n : ℕ} 
    (hmn : 2 * m ^ 2 = n ^ 2) 
  : 2 ∣ m :=
  begin
    sorry,
  end

  -- Assume that everything above this line is true.

  --BEGIN--
  
  /-
  theorem nat.not_coprime_of_dvd_of_dvd  : 1 < d → d ∣ m → d ∣ n → ¬m.coprime n
  -/

  theorem sqrt2_irrational' : 
    ¬ ∃ (m n : ℕ),
    2 * m^2 = n^2 ∧ 
    m.coprime n 
  :=
  begin
    rintro ⟨m, n, hmn, h_cop⟩,
    -- these brackets let you combine ``rintro`` with (several iterations of) ``cases``
    -- try using ``rintro h`` and then ``rcases h with ⟨m, n, hmn, h_cop⟩,`` instead
    -- you get the brackets by typing ``\langle`` and ``\rangle``
    sorry,
  end

  --END--

  

Lemmas for proving (*) assuming m ≠ 0
------------------------------------------------------------------------------
.. code:: lean 
  :name: nonzero_lemmas

  import tactic
  import data.nat.basic
  import data.nat.prime


  noncomputable theory
  open_locale classical

  open nat 


  theorem sqrt2_irrational' : 
    ¬ ∃ (m n : ℕ),
    2 * m^2 = n^2 ∧ 
    m.coprime n 
  :=
  begin
    sorry,
  end

  -- Assume that everything above this line is true.

  --BEGIN--

  /-
  pow_pos : ∀ {a : ℕ}, 0 < a → ∀ (n : ℕ), 0 < a ^ n
  -/
  lemma ge_zero_sq_ge_zero {n : ℕ} (hne : 0 < n) : (0 < n^2)
  :=
  begin
    sorry,
  end

  /-
  nat.mul_left_inj : ∀ {a b c : ℕ}, 0 < a → (b * a = c * a ↔ b = c)
  -/
  lemma cancellation_lemma {k m n : ℕ}
  (hk_pos : 0 < k^2)
  (hmn : 2 * (m * k) ^ 2 = (n * k) ^ 2)
  : 2 * m ^ 2 = n ^ 2
  :=
  begin
    sorry,
  end

  --END--


Prove (*) assuming m ≠ 0
------------------------------------------------------------------------------
.. code:: lean
  :name: assume_nonzero 

  import tactic
  import data.nat.basic
  import data.nat.prime


  noncomputable theory
  open_locale classical

  open nat 


  theorem sqrt2_irrational' : 
    ¬ ∃ (m n : ℕ),
    2 * m^2 = n^2 ∧ 
    m.coprime n 
  :=
  begin
    sorry,
  end

  lemma ge_zero_sq_ge_zero {n : ℕ} (hne : 0 < n) : (0 < n^2)
  :=
  begin 
    sorry,
  end 

  lemma cancellation_lemma {k m n : ℕ}
  (hk_pos : 0 < k^2)
  (hmn : 2 * (m * k) ^ 2 = (n * k) ^ 2)
  : 2 * m ^ 2 = n ^ 2
  := 
  begin 
    sorry,
  end 

  -- Assume that everything above this line is true.

  --BEGIN--
  /-
  gcd_pos_of_pos_left : ∀ {m : ℕ} (n : ℕ), 0 < m → 0 < m.gcd n
  gcd_pos_of_pos_right : ∀ (m : ℕ) {n : ℕ}, 0 < n → 0 < m.gcd n
  exists_coprime : ∀ {m n : ℕ}, 0 < m.gcd n → (∃ (m' n' : ℕ), m'.coprime n' ∧ m = m' * m.gcd n ∧ n = n' * m.gcd n)
  nat.pos_of_ne_zero : ∀ {n : ℕ}, n ≠ 0 → 0 < n

  -/
  theorem wlog_coprime :
    (∃ (m n : ℕ),
    2 * m^2 = n^2 ∧
    m ≠ 0 )
    → (∃ (m' n' : ℕ),
      2 * m'^2 = n'^2 ∧
      m'.coprime n' )
  :=
  begin
    rintro ⟨m, n, hmn, hm0⟩,
    set k := m.gcd n with hk,
    -- this abbreviation reduces clutter
    -- ``set`` is similar to ``have``
    -- you can replace all the ``m.gcd n`` with ``k`` using ``rw ←hk,`` if needed
    sorry,
  end

  theorem sqrt2_irrational'' : 
    ¬ ∃ (m n : ℕ),
    2 * m^2 = n^2 ∧ 
    m ≠ 0
  :=
  begin
    sorry,
  end

  --END--

