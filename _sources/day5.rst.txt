.. _day5:

***************************
Bits & Pieces
***************************

Namespaces 
===========


Lean provides us with the ability to group definitions into nested, hierarchical *namespaces*:

.. code-block:: lean
  :name: namespace_example

  namespace mcsp
    def tau := "TAU on T-F from 2-4"
    #eval tau
  end mcsp

  def tau := "no TAU on S"
  #eval tau
  #eval mcsp.tau

  open mcsp

  #eval tau -- error
  #eval mcsp.tau

When we declare that we are working in the namespace ``mcsp``, every identifier we declare has a full name with prefix "``mcsp``". 
Within the namespace, we can refer to identifiers by their shorter names, but once we end the namespace, we have to use the longer names.

The ``open`` command brings the shorter names into the current context. Often, when we import a theory file, we will want to open one or more of the namespaces it contains, to have access to the short identifiers. 
Further if ``x`` is a term of type ``nat`` and ``f`` is a term defined in namespace ``nat`` then ``nat.f x`` can be shortened to ``x.f``.
Note that ``ℕ`` is just another notation for ``nat``.

Coercions 
===========
In type theory every term has a type and two terms of different types cannot be equal to each other.
This makes it impossible to write statements like ``|m|^2 = m^2`` where ``m : ℤ`` and ``|m| : ℕ`` is the absolute value of ``m``.
But in math, we do want this statement to be true!
The round about way to deal with this is through *coercions*.
Lean will coerce the above equality to live entirely in integers as, ``↑|m|^2 = m^2``. 
This is done using an injective function ``ℕ → ℤ``.

Sometimes it is possible (and necessary) to get rid of the coercions. 
For example, say we start out with ``↑|m|^2 = m^2`` and eventually reduce it to ``↑|m|^2 = ↑1``.
The tactic for getting rid of coercions is ``norm_cast`` which will reduce the above expression to ``|m|^2 = 1``.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``norm_cast``
    - ``norm_cast,`` tries to clear out coercions.

      ``norm_cast at hp,`` tries to clear out coercions at the hypothesis ``hp``.


.. code:: lean 
  :name: coercions

  import tactic data.nat.basic data.int.basic 
  noncomputable theory 
  open_locale classical 

  theorem sqrt2_irrational_nat : 
    ¬ ∃ (m n : ℕ),
    2 * m^2 = n^2 ∧ 
    m ≠ 0
  :=
  begin
    sorry,
  end

  -- Assume the above theorem

  lemma num_2 : (2 : ℚ).num = 2 := 
  begin 
    sorry,
  end

  lemma denom_2 : (2 : ℚ).denom = 1 := 
  begin 
    sorry,
  end

  /-
  q.denom = denominator of q (valued in ℕ)
  q.num = numerator of q (valued in ℤ)

  for integer m,
  m.nat_abs = absolute value of m (valued in ℕ)

  int.nat_abs_mul_self' : ∀ (a : ℤ), ↑(a.nat_abs) * ↑(a.nat_abs) = a * a
  int.coe_nat_inj : ∀ {m n : ℕ}, ↑m = ↑n → m = n

  rat.mul_self_denom : ∀ (q : ℚ), (q * q).denom = q.denom * q.denom
  rat.mul_self_num : ∀ (q : ℚ), (q * q).num = q.num * q.num
  rat.denom_ne_zero : ∀ (q : ℚ), q.denom ≠ 0
  
  lemmas about nat-to-int coercion, which norm_cast knows:
  nat.cast_one : ↑(1 : ℕ) = (1 : ℤ)
  nat.cast_two : ↑(2 : ℕ) = (2 : ℤ)
  nat.cast_mul (m n : ℕ) : ↑(m * n) = ↑m * ↑n

  lemma which ring_nf knows:
  pow_two (x) : x^2 = x * x

  -/

  theorem sqrt2_irrational : 
  ¬ (∃ q : ℚ, 2 = q * q) 
  :=
  begin
    rintro ⟨q, h⟩,
    have clear_denom := rat.eq_iff_mul_eq_mul.mp h,
    sorry,
  end

Type classes
===========================
Type classes are used to construct complex mathematical structures. 
Any family of types can be marked as a type class. 
We can then declare particular elements of a type class to be instances.
You can think of a type class as "template" for constructing particular instances.

Consider the example of groups.
A group is defined a type class with the following attributes. 

.. code:: 

  structure group : Type u → Type u
  fields:
  group.mul : Π {α : Type u} [c : group α], α → α → α
  group.mul_assoc : ∀ {α : Type u} [c : group α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
  group.one : Π {α : Type u} [c : group α], α
  group.one_mul : ∀ {α : Type u} [c : group α] (a : α), 1 * a = a
  group.mul_one : ∀ {α : Type u} [c : group α] (a : α), a * 1 = a
  group.inv : Π {α : Type u} [c : group α], α → α
  group.mul_left_inv : ∀ {α : Type u} [c : group α] (a : α), a⁻¹ * a = 1

If you look at the `source code <https://github.com/leanprover-community/mathlib/blob/e52108d/src/algebra/group/defs.lean>`__ you'll see that the ``class group`` is built gradually by extending multiple classes.

.. code:: 
  
  class has_one      (α : Type u) := (one : α)
  -- a group has an identity element 

  class has_mul      (α : Type u) := (mul : α → α → α)
  -- a group has multiplication 

  class has_inv      (α : Type u) := (inv : α → α)
  -- a group has an inverse function

  class semigroup (G : Type u) extends has_mul G :=
  (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
  -- the multiplication is associative 

  class monoid (M : Type u) extends semigroup M, has_one M :=
  (one_mul : ∀ a : M, 1 * a = a) (mul_one : ∀ a : M, a * 1 = a)
  -- multiplication by one is trivial

  class group (α : Type u) extends monoid α, has_inv α :=
  (mul_left_inv : ∀ a : α, a⁻¹ * a = 1)
  -- multiplication is associative 

To define an arbitrary group ``G`` we first create it as a type ``G : Type`` and then make it an instance of ``group`` using 
``[group G]``.
You can also prove that existing types are instances of ``group`` using the ``instance`` keyword.
Type classes allow us to prove theorems in vast generalities. 
For example, any theorem about groups can immediately be applied to integers once we show that integers are an instance of ``group``.
If you look at `data.int.basic <https://github.com/leanprover-community/mathlib/blob/d1e63f3/src/data/int/basic.lean>`__ 
you'll see that first fifty lines of code prove that ``ℤ`` is an instance of several type classes.

.. code:: lean 
  :name: cyclic_group

  import group_theory.order_of_element
  import tactic

  #print classes
  #print instances inhabited

  class cyclic_group (G : Type*) extends group G :=
  (has_generator:  ∃ g : G, ∀ x : G, ∃ n : ℤ, x = g^n)

  /-
  zpow_add : ∀ {G : Type u_1} [group G] (a : G) (m n : ℤ), a ^ (m + n) = a ^ m * a ^ n
  add_comm : ∀ {G : Type u_1} [add_comm_semigroup G] (a b : G), a + b = b + a
  -/

  lemma mul_comm_of_cyclic
    {G : Type*}
    [hc: cyclic_group G]
    (g : G) 
  : ∀ a b : G, a * b = b * a :=
  begin
    have has_generator := hc.has_generator,
    sorry,
  end

Recursion and Induction
===========================
Lots of things in Lean are defined using recursion and proved using induction.
While this extends beyond just the natural numbers,
let's try some familiar examples using the natural numbers and the familiar principle of induction.

First let's see how to make a recursive definition. I'll define afunction called ``sum_first : ℕ → ℕ``
so that ``sum_first n`` is the sum of the first ``n`` natural numbers.

.. code:: lean 
  :name: sum_first_defn

  import data.nat.basic
  import tactic

  def sum_first :
    ℕ → ℕ -- the type of the function you want to define recursively
  | 0 := 0 -- the definition at 0
  | (n + 1) := sum_first n + (n + 1) -- the definition at (n + 1), which can use the definition at n

Now let's prove the famous closed formula for ``sum_first n``, using induction.
To do this, we'll want the following two tactics:

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``induction``
    - If ``n : ℕ`` is a natural number variable, ``P : ℕ → Prop`` is a property of natural numbers,
      and you want to prove ``P n`` using induction, then ``induction n using k ih,`` will create two goals.

      One has target ``P 0``, this is the base case.

      The other has target ``P (k.succ)``, where ``k.succ = k + 1``.
      (You can rewrite away the ``.succ`` with ``nat.succ_eq_add_one``.)
      You're also provided an induction hypothesis, ``ih : P k``.

  * - ``refl`` 
    - ``refl,`` proves things that are literally true by definition.
      Often this will handle your base case.

Now let's try the proof. Remember that ``rw`` can be useful for unfolding definitions.

.. code:: lean
  :name: sum_first_formula 

  import data.nat.basic
  import tactic

  /--------------------------------------------------------------------------

  ``induction``
    
    If ``n : ℕ`` is a natural number variable, ``P : ℕ → Prop`` is a property of natural numbers,
    and you want to prove ``P n`` using induction, then ``induction n using k ih,`` will create two goals.
    One is the base case, the other is the induction step.


  ``refl`` proves things that are literally true by definition.
    Often this will handle your base case.

  nat.succ_eq_add_one : ∀ (n : ℕ), n.succ = n + 1

  --------------------------------------------------------------------------/

  def sum_first :
    ℕ → ℕ -- the type of the function you want to define recursively
  | 0 := 0 -- the definition at 0
  | (n + 1) := sum_first n + (n + 1) -- the definition at (n + 1), which can use the definition at n

  theorem sum_first_formula : ∀ (n : ℕ), 2 * sum_first n = (n + 1) * n :=
  begin
    sorry,
  end

If you want more practice proving things about natural numbers, including plenty of induction, try the `Natural Number Game <https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/>`_.
