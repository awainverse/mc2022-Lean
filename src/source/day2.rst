.. _day2:

***************************
Logic in Lean - Part 2
***************************

The goal today is to wrap up the remaining bits of logic and move on to doing some "actual math".
Remember to **always save your work**. 
You might find the :doc:`Glossary of tactics<../tactics>` page and the :doc:`Pretty symbols<../symbols>` page useful.

Before we move on to new stuff, let's understand what we did yesterday. 

Behind the scenes 
==================

**A note on brackets:** 
It is not uncommon to compose half a dozen functions in Lean. 
The brackets get really messy and unwieldy. 
As such, Lean will often drop the brackets by following the following conventions.

* The function ``P → Q → R → S`` stands for ``P → (Q → (R → S))``.
* The expression ``a + b + c + d`` stands for ``((a + b) + c) + d``.

An easy way to remember this is that, arrows are bracketed on the right and binary operators on the left.

Proof irrelevance 
-------------------
It might feel a bit weird to say that a proposition has proofs as its inhabitants. 
Proofs can get huge and it seems unnecessary to have to remember not just the statement but also its proof.
This is something we don't normally do in math.
To hide this complication, in type theory there is an axiom, called *proof irrelevance*, which says that 
if ``P : Prop`` and ``hp1 hp2 : P`` then ``hp1 = hp2``. 
Taking our *analogy* with sets further, you can think of a proposition as a set which is either empty or contains a single element (false or true).
In fact, in some forms of type theory (e.g. `homotopy type theory <https://en.wikipedia.org/wiki/Homotopy_type_theory>`__) this is taken as the definition of propositions.
This is of course not true for general types. 
For example, ``0 : ℕ ≠ 1 : ℕ``. 


Proofs as functions 
--------------------

Every time you successfully construct a proof of a theorem say 

.. code:: 
  
  theorem tautology (P : Prop) : P → P :=
  begin
    rintro hp,
    refine hp,
  end

Lean constructs a *proof term* ``tautology : ∀ P : Prop, P → P`` 
(you can see this by typing ``#check tautology``).

In type theory, the *for all* quantifier, ``∀``, is a generalized function, called a `dependent function <https://en.wikipedia.org/wiki/Dependent_type>`__.
For all practical purposes, we can think of ``tautology`` as having the type ``(P : Prop) → (P → P)``.
Note that this is not a function in the classical sense of the word because the codomain ``(P → P)`` *depends* on the input variable ``P``.
If ``Q : Prop``, then ``tautology(Q)`` is a term of type  ``Q → Q``.

Consider a theorem with multiple hypothesis, say 

.. code::

  theorem hello_world (hp : P) (hq : Q) (hr : R) : S

Once we provide a proof of it, Lean will create a proof term
``hello_world : (hp:P) → (hq:Q) → (hr:R) → S``.
So that if we have terms ``hp' : P``, ``hq' : Q``, ``hr' : R``
then ``hello_world hp' hq' hr'`` (note the convenient lack of brackets) will be a term of type ``S``.


Once constructed, any term can be used in a later proof. For example,

.. code::

  example (P Q : Prop) : (P → Q) → (P → Q) :=
  begin
    refine tautology (P → Q),
  end

This is how Lean simulates mathematics.
Every time you prove a theorem using tactics a *proof term* gets created. 
Because of proof irrelevance, Lean forgets the exact content of the proof and 
only remembers its type.
All the proof terms can then be used in later proofs.
All of this falls under the giant umbrella of the `Curry--Howard correspondence <https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence>`__.

Optional Sidenote on Lambda
----------

Speaking of generalized functions, and terms, we can define the term ``tautology`` directly, without using ``rintro``:

.. code:: 
  
  theorem tautology (P : Prop) : P → P :=
  begin
    refine λ hp, hp,
  end

The ``λ``, typed ``\lambda``, plays basically the role of ``rintro``.
In general, the term ``λ x, y`` will define a (generalized) function that on input ``x``, gives output ``y``.
For instance, once we can talk about addition, ``λ x, x + 2`` will be the function that adds 2 to a given natural number.
If you want to, you can play around with using ``λ`` and ``rintro`` interchangeably.

The Law of the Excluded Middle
========================
You can prove exactly one of the following using just ``refine``, ``rintro``, and ``have``.
Can you find which one?

.. code:: lean

  import tactic

  /--------------------------------------------------------------------------

  You can prove exactly one of the following three using just 
  ``refine``, ``rintro``, and ``have``.
  
  Can you find which one?

  --------------------------------------------------------------------------/

  theorem not_not_self_imp_self (P : Prop) : ¬ ¬ P → P:=
  begin
    sorry,
  end

  theorem contrapositive_converse (P Q : Prop) : (¬Q → ¬P) → (P → Q) :=
  begin
    sorry,
  end

  example (P : Prop) : ¬ P → ¬ ¬ ¬ P :=
  begin
    sorry,
  end

This is because it is not true that ``¬ ¬ P = P`` *by definition*, after all, 
``¬ ¬ P`` is ``(P → false) → false`` which is drastically different from ``P``.
There is an extra axiom called **the law of excluded middle** which says that 
either ``P`` is inhabited or ``¬ P`` is inhabited (and there is no *middle* option) 
and so ``P ↔ ¬ ¬ P``.
Lean gives it to us in the form of ``em P : P ∨ ¬ P``, although it's not always included.
Because some mathematicians would prefer to avoid using this in their proofs, 
you have to type the lines ``noncomputable theory`` and ``open_locale classical``
near the top of the file, to show that you're ok with using all of classical logic!

.. code:: lean

  import tactic

  -- these two statements tell Lean to use the law of excluded middle as necessary
  noncomputable theory
  open_locale classical
  

  --BEGIN--


  /--------------------------------------------------------------------------

  ``em``
    
    If ``P : Prop``, then ``em P : P ∨ ¬ P`` lets you use the law of the excluded middle on ``P``.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  theorem not_not_self_imp_self (P : Prop) : ¬ ¬ P → P:=
  begin
    sorry,
  end

  theorem contrapositive_converse (P Q : Prop) : (¬Q → ¬P) → (P → Q) :=
  begin
    sorry,
  end

  example (P : Prop) : ¬ P → ¬ ¬ ¬ P :=
  begin
    sorry,
  end

  theorem principle_of_explosion (P Q : Prop) : P → (¬ P → Q) :=
  begin
    sorry,
  end

  --END--

There are more specialized tactics that combine ``false.elim`` and ``em`` with other tactics to streamline the process of dealing with negations.
You can read about them at :doc:`Glossary of tactics<../tactics>`, and if you want, you can try to shorten some of your above proofs with them.

Quantifiers 
============== 
As mentioned it the introduction, the *for all* quantifier, ``∀``, is a generalization of a function.
As such the tactics for dealing with ``∀`` are the same as those for ``→``.
(Type it as ``\forall``.)

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``have``
    - If ``hp`` is a term of type ``∀ x : X, P x`` and 
      ``y`` is a term of type ``X`` then 
      ``have hpy := hp(y)`` creates a hypothesis ``hpy : P y``.

  * - ``rintro``
    - If the target of the current goal is ``∀ x : X, P x``, then 
      ``rintro x,`` creates a hypothesis ``x : X`` and 
      changes the target to ``P x``.

The *there exists* quantifier, ``∃``, in type theory, uses similar tools to 
If you want to prove a statement ``∃ x : X, P x`` then you need to provide a witness.
If you have a term ``hp : ∃ x : X, P x`` then from this you can extract a witness.
(Type it as ``\exists``.)

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``cases``
    - If ``hp`` is a term of type ``∃ x : X, P x``, then 
      ``cases hp with x key,`` breaks it into 
      ``x : X`` and ``key : P x``.

  * - ``use``
    - If the target of the current goal is ``∃ x : X, P x`` 
      and ``y`` is a term of type ``X``, then 
      ``use y,`` changes the target to ``P y`` and tries to close the goal.

Finally, we know enough Lean to start doing some fun stuff.

Barber paradox
------------------------------------  
Let's disprove the "barber paradox" due to Bertrand Russell. 
The claim is that in a certain town there is a (male) barber that shaves all the men who do not shave themselves. (Why is this a paradox?)
Prove that this is a contradiction.
Here are some :doc:`hints <../hint_1_barber_paradox>` if you get stuck.

.. code-block:: lean

  import tactic
  -- the next two lines let us use the law of the excluded middle without trouble
  noncomputable theory
  open_locale classical

  --BEGIN--

  /--------------------------------------------------------------------------

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  -- men is type. 
  -- x : men means x is a man in the town
  -- shaves x y is inhabited if x shaves y

  variables (men : Type) (barber : men) 
  variable  (shaves : men → men → Prop)

  example : ¬ (∀ x : men, shaves barber x ↔ ¬ shaves x x) := 
    begin 
      sorry,
    end 
  --END--


Mathcampers singing paradox 
------------------------------------
  
Assume that the main lounge is non-empty.
At a fixed moment in time, there is someone in the lounge such that, 
if they are singing, 
then everyone in the lounge is singing. 
(See :doc:`hints <../hint_1_mcsp>`).

.. code:: lean
  :name: lounge_paradox

  import tactic
  -- the next two lines let us use the law of the excluded middle without trouble
  noncomputable theory
  open_locale classical

  --BEGIN--

  /--------------------------------------------------------------------------

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  -- camper is a type. 
  -- If x : camper then x is a camper in the main lounge.
  -- singing(x) is inhabited if x is singing 

  theorem math_campers_singing_paradox  
    (camper : Type) 
    (singing : camper → Prop) 
    (alice : camper) -- making sure that there is at least one camper in the lounge
    : ∃ x : camper, (singing x → (∀ y : camper, singing y)) :=
  begin
    sorry,
  end
  --END--

Relationship conundrum
-----------------------
A relation ``r`` on a type ``X`` is a map ``r : X → X → Prop``.
We say that ``x`` is *related* to ``y`` if ``r x y`` is inhabited.

* ``r`` is reflexive if ``∀ x : X``, ``x`` is related to itself.
* ``r`` is symmetric if ``∀ x y : X``, ``x`` is related to ``y`` implies ``y`` is related to ``x``.
* ``r`` is transitive if ``∀ x y z : X``, ``x`` is related to ``y`` and ``y`` is related to ``x`` implies ``z`` is related to ``z``.
* ``r`` is connected if for all ``x : X`` there is a ``y : Y`` such that ``x`` is related to ``y``.

Show that if a relation is symmetric, transitive, and connected,
then it is also reflexive.

.. code:: lean

  import tactic 
  
  variable X : Type 

  theorem reflexive_of_symmetric_transitive_and_connected
    (r : X → X → Prop)
    (h_symm : ∀ x y : X, r x y → r y x) 
    (h_trans : ∀ x y z : X, r x y → r y z → r x z) 
    (h_connected : ∀ x, ∃ y, r x y) 
  : (∀ x : X, r x x) :=
  begin
    sorry,
  end

Equality 
===========
So far we have not seen how to deal with propositions of the form ``P = Q``, for example, ``1 + 2 + ... + n = n(n + 1)/2``. Proving these propositions by hand requires messing around with the axioms of type theory.
*Using* equalities on the other hand is very easy. The rewrite tactic (usually shortened to ``rw``) let's you replace the left hand side of an equality with the right hand side.

.. list-table:: 
  :widths: 10 90
  :header-rows: 0

  * - ``rw``
    - If ``f`` is a term of type ``P = Q`` (or ``P ↔ Q``), then 

        ``rw f,`` searches for ``P`` in the target and replaces it with ``Q``.

        ``rw ←f,`` searches for ``Q`` in the target and replaces it with ``P``.
      
      Additionally, if ``hr : R`` is a hypothesis, then 

        ``rw f at hr,`` searches for ``P`` in the expression ``R`` and replaces it with ``Q``.

        ``rw ←f at hr,`` searches for ``Q`` in the expression ``R`` and replaces it with ``P``.

      Mathematically, this is saying "because ``P = Q``, we can replace ``P`` with ``Q`` (or the other way around)".

To get the left arrow, type ``\l``. If you want to rewrite a bunch of things in a row, you can type ``rw [h1, h2, h3],``.

.. code:: lean 

  import tactic data.nat.basic
  open nat 

  /--------------------------------------------------------------------------

    ``rw``
      
      If ``f`` is a term of type ``P = Q`` (or ``P ↔ Q``), then 
      ``rw f`` replaces ``P`` with ``Q`` in the target.
      Other variants:
        ``rw f at hp``, ``rw ←f``, ``rw ←f at hr``.

    Delete the ``sorry,`` below and replace them with a legitimate proof.

    --------------------------------------------------------------------------/

  theorem add_self_self_eq_double 
    (x : ℕ) 
  : x + x = 2 * x := 
  begin 
    rw two_mul,
  end 

  /-
  For the following problem, use 
    mul_comm a b : a * b = b * a 
  -/

  example (a b c d : ℕ)
    (hyp : c = d * a + b)
    (hyp' : b = a * d)
  : c = 2 * (a * d) :=
  begin
    sorry,
  end

  /-
  For the following problem, use 
    nat.sub_self (x : ℕ) : x - x = 0
  -/

  example (a b c d : ℕ)
    (hyp : c = b * a - d)
    (hyp' : d = a * b)
  : c = 0 :=
  begin
    sorry,
  end


Surjective functions
----------------------
Recall that a function ``f : X → Y`` is surjective if for every ``y : Y`` there exists a term ``x : X``
such that ``f(x) = y``. 
In type theory, for every function ``f`` we can define a corresponding proposition 
``surjective (f) := ∀ y, ∃ x, f x = y`` and a function being surjective is equivalent to saying that the proposition ``surjective(f)`` is inhabited.

.. code:: lean 

  import tactic 
  open function

  /--------------------------------------------------------------------------

  ``rw``

    If it gets hard to keep track of the definition of ``surjective``, 
    you can use ``rw surjective,`` or ``rw surjective at h,`` 
    to get rid of it. (This rewrites using the definition of surjective).
    Typing ``rw surjective at *,`` will unfold it
    everywhere at once.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

  variables X Y Z : Type
  variables (f : X → Y) (g : Y → Z)

  /-
  surjective (f : X → Y) := ∀ y, ∃ x, f x = y

  You may also want to try ``function.comp_app``
  -/

  example 
    (hf : surjective f) 
    (hg : surjective g) 
    : surjective (g ∘ f) :=
  begin
    sorry,
  end

  example 
    (hgf : surjective (g ∘ f)) 
    : surjective g :=
  begin
    sorry,
  end
