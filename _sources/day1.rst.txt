.. _day1:

************************
Logic in Lean - Part 1
************************

Today's goal is to understand the philosophy of type theory (in Lean).
Don't try to memorize anything, that will happen automatically. 
Instead, try to do as many exercises as you can. 
Practice is the only way to learn a new programming language.
And **always save your work**. 
The easiest way to do this in the browser is by bookmarking the Lean page, which contains your code in its URL.

Lean is built on top of a logic system called *type theory*, which is an alternative to *set theory*.
In type theory, instead of elements we have *terms* and every term has a *type*.
When translated to math, terms can be either mathematical objects, functions, propositions, or proofs. 
The notation ``x : X`` stands for "``x`` is a term of type ``X``" or "``x`` is an inhabitant of ``X``".
For the most part, you can think of a type as a set and terms as elements of the set.

Propositions as types
======================

In set theory, a **proposition** is any statement that has the potential of being true or false, like ``2 + 2 = 4``, ``2 + 2 = 5``, "Fermat's last theorem", or "Riemann hypothesis".
In type theory, there is a special type called ``Prop`` whose inhabitants are propositions.
Furthermore, each proposition ``P`` is itself a type and the inhabitants of ``P`` are its proofs!

.. code::

    P : Prop     -- P is a proposition
    hp : P       -- hp is a proof of P

As such, in type theory "producing a proof of ``P``" is the same as "producing a term of type ``P``"
and so a proposition ``P`` is ``true`` if there exists a term ``hp`` of type ``P``.

**Notation.** Throughout these notes, ``P, Q, R, ...`` will denote propositions.

Propositions in Lean 
---------------------
In Lean, a proposition and its proof are written using the following syntax.

.. code:: lean
  :name: flt

  theorem fermats_last_theorem 
    (n : ℕ) 
    (n_gt_2 : n > 2) 
    : 
    ¬ (∃ x y z : ℕ, (x^n + y^n = z^n) ∧ (x ≠ 0) ∧ (y ≠ 0) ∧ (z ≠ 0))
  := 
  begin 
    sorry,
  end


Let us parse the above statement. (Lean ignores multiple whitespaces, tabs, and new lines. 
You could theoretically write the entire code in a single line. Please don't.)

* ``fermats_last_theorem`` is the name of the theorem. 
* ``(n : ℕ)`` and ``(n_gt_2 : n > 2)`` are the two *hypotheses*. 
  The former says ``n`` is a natural number and the latter says that ``n_gt_2`` is a proof of ``n > 2``.
* ``:`` is the delimiter between hypotheses and targets
* ``¬ (∃ x y z : ℕ, (x^n + y^n = z^n) ∧ (x ≠ 0) ∧ (y ≠ 0) ∧ (z ≠ 0))`` is the *target* of the theorem.
  We'll learn all these symbols soon.
* ``:= begin ... end`` contains the proof. When you start your proof, Lean opens up a goal window  for you to keep track of hypotheses and targets. 
  **Your goal is to produce a term that has the type of the target**.

  .. code:: 

    -- example of Lean goal window
    n : ℕ, -- hypothesis 1
    n_gt_2 : n > 2 -- hypothesis 2
    ⊢ ¬∃ (x y z : ℕ), x ^ n + y ^ n = z ^ n ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 -- target

* The commands you write between ``begin`` and ``end`` are called *tactics*. 
  ``sorry,`` is an example of a tactic. 
  **Very Important:** All tactics must end with a comma (,) .

Even though they are not explicitly displayed, 
all the theorems in the Lean library are also hypotheses that you can use to close the goal. 


Implication 
------------
In set theory, the proposition ``P ⇒ Q`` ("P implies Q") is true if either both ``P`` and ``Q`` are true or if ``P`` is false. 
In type theory, a proof of an implication ``P ⇒ Q`` is just a function ``f : P → Q``.
Given a function ``f : P → Q``, every proof ``hp : P`` produces a proof ``f(hp) : Q``.
If ``P`` is false then ``P`` is *empty*, and there exists an `empty function <https://en.wikipedia.org/wiki/Function_(mathematics)#empty_function>`_ from an empty type to any type.
Hence, in type theory we use ``→`` to denote implication. (Type it in Lean editors with ``\to``.)

Implications in Lean 
======================
We'll start learning tactics by proving implications in Lean.
In the following sections, there are tables describing what a tactic does. 
Solve the following exercises to see the tactics in action.

The first two tactics we'll learn are ``refine`` and ``rintro``. 

.. list-table:: 
   :widths: 20 80
   :header-rows: 0

   * - ``refine``
     - If ``P`` is the target of the current goal 
       and ``hp`` is a term of type ``P``,  
       then ``refine hp,`` will close the goal.

       Mathematically, this saying "this is what we were required to prove".

   * - ``rintro``
     - If the target of the current goal is a function ``P → Q``, 
       then ``rintro hp,`` will produce a hypothesis 
       ``hp : P`` and change the target to  ``Q``.

       Mathematically, this is saying that in order to define a function from ``P`` to ``Q``,
       we first need to choose (introduce) an arbitrary element of ``P``.

       If you want to use this repeatedly, you can type ``rintro h1 h2`` instead of ``rintro h1,`` and then ``rintro h2,``.

.. code:: lean
  :name: refine_rintro_examples

  import tactic
  /--------------------------------------------------------------------------

  ``refine``
    
    If ``P`` is the target of the current goal 
    and ``hp`` is a term of type ``P``,  
    then ``refine hp,`` will close the goal.


  ``rintro``

    If the target of the current goal is a function ``P → Q``, then 
    ``rintro hp,`` will produce a hypothesis 
    ``hp : P`` and change the target to  ``Q``.

  Delete the ``sorry,`` below and replace them with a legitimate proof.
       
  --------------------------------------------------------------------------/
  
  theorem tautology (P : Prop) (hp : P) : P :=
  begin
    sorry, 
  end

  theorem tautology' (P : Prop) : P → P :=
  begin
    sorry,
  end

  example (P Q : Prop): (P → (Q → P)) := 
  begin 
    sorry,
  end 

  -- Can you find two different ways of proving the following?
  example (P Q : Prop) : ((Q → P) → (Q → P)) := 
  begin 
    sorry,
  end 

We know how to start a proof, and how to finish a proof, but what about partial progress?
Here's two approaches.
One uses a new tactic, ``have``, for forward reasoning,
and the other uses ``refine`` again for backward reasoning.

In both of these cases, if ``f`` is a term of type ``P → Q``, then we can think of ``f`` as a function,
sending proofs of ``P`` to proofs of ``Q``.
If ``hp`` is a term of type ``P``, we can literally write ``f (hp)``, although often we can skip the parentheses and just write ``f hp``.

.. list-table:: 
   :widths: 20 80
   :header-rows: 0

   * - ``have``
     - ``have`` is used to create intermediate variables. 
     
       If ``f`` is a term of type ``P → Q`` and 
       ``hp`` is a term of type ``P``, then
       ``have hq := f hp,`` creates the hypothesis ``hq : Q`` .

   * - ``refine``
     - ``refine`` can be used for backward reasoning. 

       If the target of the current goal is ``Q`` and 
       ``f`` is a term of type ``P → Q``, then 
       ``refine f _,`` changes target to ``P``.

       Mathematically, this is equivalent to saying "because ``P`` implies ``Q``, to prove ``Q`` it suffices to prove ``P``".
       The ``_`` stands in for a proof of ``P`` that we will provide later.

Often these two tactics can be used interchangeably.
When writing a big proof, you often want a healthy combination of the two that makes the proof readable.

.. code:: lean 
  :name: have_refine_examples

  import tactic
  /--------------------------------------------------------------------------

  ``have``
    
    If ``f`` is a term of type ``P → Q`` and 
    ``hp`` is a term of type ``P``, then
    ``have hq := f hp ,`` creates the hypothesis ``hq : Q`` .


  ``refine``

    If the target of the current goal is ``Q`` and 
       ``f`` is a term of type ``P → Q``, then 
       ``refine f _,`` changes target to ``P``.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  example (P Q R : Prop) (hp : P) (f : P → Q) (g : Q → R) : R :=
  begin
    sorry,
  end

  example (P Q R S T U: Type)
  (hpq : P → Q)
  (hqr : Q → R)
  (hqt : Q → T)
  (hst : S → T)
  (htu : T → U)
  : P → U :=
  begin
    sorry,
  end

We will be learning a lot of tactics this week.
If ever you lose track of them, check out the :doc:`Glossary of tactics<../tactics>`,
which lists all of the tactics that are mentioned in these notes,
as well as some others which are not needed for this class, but may come up if you read other code in Lean.

And / Or
===============================
The operators *and* (``∧``) and *or* (``∨``) are easy to use in Lean.
(You can type them in Lean editors with ``\and`` and ``\or``.)
Given a term ``hpq : P ∧ Q``, 
there are tactics that let you 
create terms ``hp : P`` and ``hq : Q``, and vice versa.
Similarly for ``P ∨ Q``, with a subtle change (see below).

**Note** that when multiple goals are open, you are trying to solve the topmost goal.
The easiest way to keep track of multiple goals is with brackets.
After you use a tactic with multiple goals, you should use ``{ },`` to bracket off your attempt to solve the first goal,
and ``{ },`` to bracket off your second goal.
Then if you put your cursor in between the brackets, the goal monitor on the right should only display one goal at a time!


.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``cases``
    - ``cases`` is a general tactic that breaks a complicated term into simpler ones.

      If ``hpq`` is a term of type ``P ∧ Q``, then 
      ``cases hpq with hp hq,`` breaks it into ``hp : P`` and ``hp : Q``.

      If ``fg`` is a term of type ``P ↔ Q``, then 
      ``cases fg with f g,`` breaks it into ``f : P → Q`` and ``g : Q → P``.
      (This is because ``P ↔ Q`` is actually shorthand for ``(P → Q) ∧ (Q → P)``.)

      If ``hpq`` is a term of type ``P ∨ Q``, then 
      ``cases hpq with hp hq,`` creates two goals and adds the hypotheses ``hp : P`` and ``hq : Q`` to one each.

  * - ``split``
    - ``split`` is a general tactic that breaks a complicated goal into simpler ones.
    
      If the target of the current goal is ``P ∧ Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``P`` and ``Q``.

      If the target of the current goal is ``P ↔ Q``, then 
      ``split,`` breaks up the goal into two goals with targets ``P → Q`` and ``Q → P``.

  * - ``left``
    - If the target of the current goal is ``P ∨ Q``, then 
      ``left,`` changes the target to ``P``.
  
  * - ``right``
    - If the target of the current goal is ``P ∨ Q``, then 
      ``right,`` changes the target to ``Q``.


.. code:: lean
  :name: and_or_example

  import tactic

  --BEGIN--


  /--------------------------------------------------------------------------

  ``cases``
    
    ``cases`` is a general tactic that breaks up complicated terms.
    If ``hpq`` is a term of type ``P ∧ Q`` or ``P ∨ Q`` or ``P ↔ Q``, then use 
    ``cases hpq with hp hq,``.

  ``split``
    
    If the target of the current goal is ``P ∧ Q`` or ``P ↔ Q``, then use
    ``split,``.

  ``left``/``right``
    
    If the target of the current goal is ``P ∨ Q``, then use 
    either ``left,`` or ``right,`` (choose wisely).

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  theorem bracket_example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  begin
    split,
    {
      sorry,
    },
    {
      sorry,
    }
  end

  example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  begin
    sorry,
  end

  example (P Q : Prop) : P ∨ Q → Q ∨ P :=
  begin
    sorry,
  end

  --END--

Optional Sidenote on Brackets
----------

We've discussed that building a term of type ``P`` is pretty much the same thing as providing a proof of ``P``.
We've also seen that if you want to provide a term of type ``P ∧ Q``, all you need is a term ``hp : P``, a term ``hq : Q``, and the ``split`` tactic.
However, you don't *need* the ``split`` tactic for this, you can also build the term directly, using the angle brackets ``⟨⟩``, typed with ``\langle`` and ``\rangle``.
For example:

.. code::

    example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
    begin
      refine ⟨hp, hq⟩,
    end

This works because ``⟨hp, hq⟩`` is a term of type ``P ∧ Q``, because Lean defines ``P ∧ Q`` to be the type of ordered pairs, consisting of a term of type ``P`` and then a term of type ``Q``.
If you want to explore this, try using this to rewrite your above proofs that use ``∧``.
(If you do, what does ``refine ⟨_, _⟩,`` do?)

Negation 
===============

In type theory, there is a special proposition ``false : Prop`` which has no proof (hence is *empty*).
The negation of a proposition ``¬ P`` is the implication ``P → false``.
Such a function exists if and only if ``P`` itself is empty (`empty function <https://en.wikipedia.org/wiki/Function_(mathematics)#empty_function>`_), hence ``P → false`` is inhabited if and only if ``P`` is empty which justifies using it as the definition of ``¬ P``.
(Type ``¬`` it as ``\not``.)

**To summarize:**
  1. Proving a proposition ``P`` is equivalent to producing an inhabitant ``hp : P``. 
  2. Proving an implication ``P → Q`` is equivalent to producing a function ``f : P → Q``.
  3. The negation, ``¬ P``, is defined as the implication ``P → false``.


For the following exercises, recall that ``¬ P`` is defined as ``P → false``,
``¬ (¬ P)`` is ``(P → false) → false``, and so on.
Here are some :doc:`hints <../hint_1_negation_exercises>` if you get stuck.

.. code:: lean
  :name: negation_examples

  import tactic
  /--------------------------------------------------------------------------

  Recall that 
    ``¬ P`` is ``P → false``,
    ``¬ (¬ P)`` is ``(P → false) → false``, and so on.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  theorem self_imp_not_not_self (P : Prop) : P → ¬ (¬ P) :=
  begin
    sorry,
  end

  theorem contrapositive (P Q : Prop) : (P → Q) → (¬Q → ¬P) :=
  begin
    sorry,
  end

  example (P : Prop) : ¬ (¬ (¬ P)) → ¬ P :=
  begin
    sorry,
  end

Now that we're working with negations, we can start to talk about everybody's favorite or least favorite proof technique, contradiction.
Or at least, a version of it called the `"Principle of Explosion" <https://en.wikipedia.org/wiki/Principle_of_explosion>`__.
This says that you can derive any fact from a contradiction.
In Lean, this is written as ``false → P``, and whenever you need it, there is a hypothesis ``false.elim : false → P``, which works *for any* ``P : Prop``.

.. code:: lean
  :name: explosion_examples

  import tactic
  /--------------------------------------------------------------------------

  Recall that for any ``P : Prop``, you can use ``false.elim : false → P``
    to prove ``P`` from a contradiction.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  example (P Q R : Prop) : P ∧ false ↔ false :=
  begin
    sorry,
  end

  theorem principle_of_explosion (P Q : Prop) : P ∧ ¬ P → Q :=
  begin
    sorry,
  end

Final Remarks
===============

You might be wondering, if type theory is so cool why have I not heard of it before?

Many programming languages highly depend on type theory (that's where the term ``datatype`` comes from). 
Once you define a term ``x : ℕ``, a computer can immediately check that all the manipulations you do with ``x`` 
are valid manipulations of natural numbers (so you don't accidentally divide by 0 [#f1]_ , for example).

Unfortunately, this also means that the term ``1 : ℕ`` is different from the term ``1 : ℤ``.
In Lean, if you do ``(1 : ℕ - 2 : ℕ)`` you get ``0 : ℕ`` but if you do ``(1 : ℤ - 2 : ℤ)`` you get ``-1 : ℤ``,
that's because natural numbers and subtraction are not buddies.
Another issue is that ``1 : ℕ = 1 : ℤ`` is not a valid statement in type theory.
This is not the end of the world though. 
Lean allows you to *coerce* ``1 : ℕ`` to ``1 : ℤ`` if you want subtraction to work properly, 
or ``1 : ℕ`` to ``1 : ℚ`` if you want division to work properly.

This, and a few other such things, is what drives most mathematicians away from type theory.
But these things are only difficult when you're first learning them.
With practice, type theory becomes second nature, the same as set theory.
In fact, the exact type theoretic system Lean uses is *equiconsistent*  with a slightly stronger version of ZFC, the generally-accepted axiom system for set theory.
(See `Mario Carneiro's MS thesis <https://github.com/digama0/lean-type-theory/releases/tag/v1.0>`__)

.. rubric:: footnotes

.. [#f1] Except under staff supervision.