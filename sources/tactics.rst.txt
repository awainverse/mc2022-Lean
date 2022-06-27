.. _tactics:

*********************
Glossary of Tactics and Lemmas 
*********************

Here's a summary of all the tactics and some of the lemmas we will introduce in this class, as well as some other common ones you may encounter.

Implications in Lean 
============== 

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``refine``
    - If ``P`` is the target of the current goal 
      and ``hp`` is a term of type ``P``,  
      then ``refine hp,`` will close the goal.

      Mathematically, this saying "this is what we were required to prove".

      If you can't fully close a goal, but want to work somewhat from the end, you can use ``_`` to fill in the missing pieces.
      For instance, if the target of the current goal is ``Q`` and 
      ``f`` is a term of type ``P → Q``, then
      ``refine f _,`` changes the target to ``P``.

      If you can fully close a goal, you can also type ``exact hp,``, which does pretty much the same thing.

  * - ``rintro``
    - If the target of the current goal is a function ``P → Q``, 
      then ``rintro hp,`` will produce a hypothesis 
      ``hp : P`` and change the target to  ``Q``.

      Mathematically, this is saying that in order to define a function from ``P`` to ``Q``,
      we first need to choose (introduce) an arbitrary element of ``P``.

      If you want to use this repeatedly, you can type ``rintro h1 h2`` instead of ``rintro h1,`` and then ``rintro h2,``.
      If you want to use this to introduce a variable of a more complicated type that you would then apply ``cases`` to,
      you can try something like ``rintro ⟨x1, x2, x3⟩,`` where ``⟨⟩`` are typed with ``\langle` and ``\rangle``.
   
  * - ``have``
    - ``have`` is used to create intermediate variables. 
     
      If ``f`` is a term of type ``P → Q`` and 
      ``hp`` is a term of type ``P``, then
      ``have hq := f(hp),`` creates the hypothesis ``hq : Q`` .

      You can also create subgoals with ``have hp : P,`` which will create a separate goal to prove ``P``.
      Once you have closed this goal, you'll have the hypothesis ``hp : P`` at your disposal.
     
  * - ``apply``
    - ``apply`` is used for backward reasoning. 

      If the target of the current goal is ``Q`` and 
      ``f`` is a term of type ``P → Q``, then 
      ``apply f,`` changes target to ``P``.

      Mathematically, this is equivalent to saying "because ``P`` implies ``Q``, to prove ``Q`` it suffices to prove ``P``".
      This is similar to using ``refine _,``.


And / Or
============== 

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``cases``
    - ``cases`` is a general tactic that breaks a complicated term into simpler ones.

      If ``hpq`` is a term of type ``P ∧ Q``, then 
      ``cases hpq with hp hq,`` breaks it into ``hp : P`` and ``hp : Q``.

      If ``hpq`` is a term of type ``P × Q``, then 
      ``cases hpq with hp hq,`` breaks it into ``hp : P`` and ``hp : Q``. 

      If ``fg`` is a term of type ``P ↔ Q``, then 
      ``cases fg with f g,`` breaks it into ``f : P → Q`` and ``g : Q → P``.

      If ``hpq`` is a term of type ``P ∨ Q``, then 
      ``cases hpq with hp hq,`` creates two goals and adds the hypotheses ``hp : P`` and ``hq : Q`` to one each.

  * - ``split``
    - ``split`` is a general tactic that breaks a complicated goal into simpler ones.
    
      If the target of the current goal is ``P ∧ Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``P`` and ``Q``.

      If the target of the current goal is ``P × Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``P`` and ``Q``.

      If the target of the current goal is ``P ↔ Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``P → Q`` and ``Q → P``.

      You can also accomplish this with ``refine ⟨_, _⟩``.

  * - ``left``
    - If the target of the current goal is ``P ∨ Q``, then 
      ``left,`` changes the target to ``P``.
    
  * - ``right``
    - If the target of the current goal is ``P ∨ Q``, then 
      ``right,`` changes the target to ``Q``.
    
  * - ``rcases``
    - ``rcases`` is a more general form of ``cases``. Needs the symbols ``⟨⟩``, which are typed with ``\langle`` and ``\rangle``.

      For an example, say you have ``h : ∃ (m n : ℕ), 2 * m ^ 2 = n ^ 2 ∧ 0 < m``.
      Then you can type ``rcases h with ⟨m, n, hmn, hme0⟩,`` to break ``h`` into its 4 component parts.


Negations and Proof by Contradiction
============== 

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``false.elim``
    - Not a tactic, but a lemma.

      If ``P : Prop``, then ``false.elim : false → P`` lets you prove ``P`` from a contradiction.

  * - ``exfalso``
    - Changes the target of the current goal to ``false``.
      
      The name derives from `"ex falso, quodlibet" <https://en.wikipedia.org/wiki/Principle_of_explosion>`__ which translates to "from contradiction, anything". 
      You should use this tactic when there are contradictory hypotheses present. 

  * - ``em``
    - Not a tactic, but a lemma.

      If ``P : Prop``, then ``em P : P ∨ ¬ P`` lets you use the law of the excluded middle on ``P``.

  * - ``by_cases``
    - If ``P : Prop``, then ``by_cases hp : P,`` creates two goals, 
      the first with a hypothesis ``hp: P`` and second with a hypothesis ``hp: ¬ P``.

      This lets you use the law of the excluded middle, combining ``em`` with ``cases``.

  * - ``by_contradiction``
    - If the target of the current goal is  ``Q``,
      then ``by_contradiction,`` changes the target to  ``false`` and 
      adds ``hnq : ¬ Q`` as a hypothesis.

      Mathematically, this is proof by contradiction.
      This is essentially a combination of ``rintro`` with ``false.elim``.
  
  * - ``push_neg``
    - ``push_neg,`` simplifies negations in the target. 
    
      For example, if the target of the current goal is ``¬ ¬ P``, then 
      ``push_neg,`` simplifies it to ``P``. 

      You can also push negations across a hypothesis ``hp : P`` using ``push_neg at hp,``.

  * - ``contrapose!``
    - If the target of the current goal is  ``P → Q``,
      then ``contrapose!,`` changes the target to  ``¬ Q → ¬ P``.

      If the target of the current goal is ``Q`` 
      and one of the hypotheses is ``hp : P``,
      then ``contrapose! hp,`` changes the target to  ``¬ P`` 
      and changes the hypothesis to ``hp : ¬ Q``.

      Mathematically, this is replacing the target by its contrapositive.


Quantifiers 
============== 

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``have``
    - If ``hp`` is a term of type ``∀ x : X, P x`` and 
      ``y`` is a term of type ``y`` then 
      ``have hpy := hp(y)`` creates a hypothesis ``hpy : P y``.

  * - ``rintro``
    - If the target of the current goal is ``∀ x : X, P x``, then 
      ``rintro x,`` creates a hypothesis ``x : X`` and 
      changes the target to ``P x``.

  * - ``cases``
    - If ``hp`` is a term of type ``∃ x : X, P x``, then 
      ``cases hp with x key,`` breaks it into 
      ``x : X`` and ``key : P x``.

      See also ``rcases`` to avoid using ``cases`` repeatedly.

  * - ``use``
    - If the target of the current goal is ``∃ x : X, P x`` 
      and ``y`` is a term of type ``X``, then 
      ``use y,`` changes the target to ``P y`` and tries to close the goal.

      You can also use ``refine ⟨_, _⟩,`` and then you get two goals, one with target ``X``, and the other is the fact ``P y``,
      where ``y`` is the witness you entered for ``X``.
      If you already have the witness ``y``, you may type ``refine ⟨y, _⟩,``.

Proving "trivial" statements 
=============================

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``refl`` 
    - ``refl,`` proves things that are literally true by definition.

  * - ``norm_num``
    - ``norm_num`` is Lean’s calculator. If the target has a proof that involves *only* numbers and arithmetic operations,
      then ``norm_num`` will close this goal.

      If ``hp : P`` is an assumption then ``norm_num at hp,`` tries to use simplify ``hp`` using basic arithmetic operations.

  * - ``ring_nf`` 
    - ``ring_nf,`` is Lean's symbolic manipulator. 
      If the target has a proof that involves *only* algebraic operations, 
      then ``ring_nf,`` will close the goal.

      If ``hp : P`` is an assumption then ``ring_nf at hp,`` tries to use simplify ``hp`` using basic algebraic operations.

  * - ``linarith`` 
    - ``linarith,`` is Lean's inequality solver.
  
  * - ``simp`` 
    - ``simp,`` is a very complex tactic that tries to use theorems from the mathlib library to close the goal. 
      You should only ever use ``simp,`` to *close a goal* because its behavior changes as more theorems get added to the library.
      If you really want to use ``simp,`` but it doesn't close the goal, try ``squeeze_simp,``,
      and click the instructions given in the goal window.

Equality 
===========

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``rw``
    - If ``f`` is a term of type ``P = Q`` (or ``P ↔ Q``), then 

        ``rw f,`` searches for ``P`` in the target and replaces it with ``Q``.

        ``rw ←f,`` searches for ``Q`` in the target and replaces it with ``P``.
      
      If additionally, ``hr : R`` is a hypothesis, then 

        ``rw f at hr,`` searches for ``P`` in the expression ``R`` and replaces it with ``Q``.

        ``rw ←f at hr,`` searches for ``Q`` in the expression ``R`` and replaces it with ``P``.

      Mathematically, this is saying because ``P = Q``, we can replace ``P`` with ``Q`` (or the other way around).

      You can also use this to unfold definitions, for instance if ``f : X → Y``, then
      ``rw surjective,`` will change the goal ``surjective f`` to
      ``∀ (b : Y), ∃ (a : X), f a = b``, so you can see what you're trying to prove.
      For this purpose, you could also use the tactic ``unfold``, as in ``unfold surjective,``.

Induction
===========

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