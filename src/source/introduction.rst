.. _introduction:

*****************
Introduction
*****************

What is Lean?
===============
`Lean <https://leanprover.github.io/about/>`__ is an open source proof-checker and a proof-assistant. 
One can *explain* mathematical proofs to it and it can check their correctness.
It also simplifies the proof writing process by providing ``goals`` and ``tactics``.

Lean is built on top of a formal system called type theory.
In type theory, the basic notions are "terms" and "types" --- compare to "elements" and "sets" in set theory.
Every term has a type, and types are just a special kind of term.
Terms can be interpreted as mathematical objects, functions, propositions, or proofs.
The only two things Lean can do is *create* terms and *check* their types.
By iterating these two operations, we can teach Lean to verify complex mathematical proofs.

.. code-block:: lean
  :name: easy_fermat

  import data.nat.basic

  def x := 2 + 2                                  -- a natural number
  def f (x : ℕ) := x + 3                          -- a function
  def easy_theorem_statement := 2 + 2 = 4         -- a proposition
  def fermats_last_theorem_statement              -- another proposition
    :=
    ∀ n : ℕ,
    n > 2
    →
    ¬ (∃ x y z : ℕ, (x^n + y^n = z^n) ∧ (x ≠ 0) ∧ (y ≠ 0) ∧ (z ≠ 0))

  theorem
  easy_proof : easy_theorem_statement             -- proof of easy_theorem
  :=
  begin
    rw easy_theorem_statement,                    -- a tactic
  end

  theorem 
  hard_proof : fermats_last_theorem_statement     -- cheating!
  :=
  begin
    sorry,
  end

  #check x
  #check f
  #check easy_theorem_statement
  #check fermats_last_theorem_statement 
  #check easy_proof
  #check hard_proof


How to use these notes 
=========================
Every once in a while, you will see a code snippet like this:

.. code-block:: lean
  :name: hello_world

    #eval "Hello, World!"

Clicking on the ``try it!`` button in the upper right corner will
open a copy in a window
so that you can edit it,
and Lean provides feedback in the ``Lean Infoview`` window.
We use this feature to provide exercises inline in the notes. 
We recommend attempting each exercise as you go along.

If you have installed Lean, then you can type the following in your command line to download the exercises.
(If you are not used to using the command line, ask for help!)
``leanproject get awainverse/mc2022-lean-examples``
This will create a folder called ``mc2022-lean-examples``.
You should then the folder in VSCode by typing ``code mc2022-lean-examples``.

These notes are designed for a 5-day Lean crash course at Mathcamp 2022, based on a similar class at Mathcamp 2020.
On Days 1 and 2 you'll learn the basics of type theory and some basic ``tactics`` in Lean. 
On Days 3, 4, 5 you'll use these to prove increasingly complex theorems, namely the infinitude of primes and irrationality of :math:`\sqrt{2}`.

These notes provide a sneak-peek into the world of theorem proving in Lean and are by no means comprehensive.
It is recommended that you simultaneously attempt at least one of the following two options.

#. Play the `Natural Number Game`_.
#. Read `Theorem Proving in Lean`_.

The `Natural Number Game`_ is a fun game that proves same basic properties of natural numbers in Lean.
`Theorem Proving in Lean`_ is a comprehensive online book that aims to cover all the theorem proving aspects of Lean in great detail. 

The Lean community is very welcoming to newcomers, and people are available on the `Lean Zulip chat group`_ round the clock
to answer questions. 
You can also join Kevin Buzzard's `Discord server <https://t.co/DSz6mbw4Oc?amp=1>`__ which has a relatively younger crowd.


Acknowledgments.
===================
These notes are developed by `Aaron Anderson <https://www.math.ucla.edu/~aaronanderson/>`__, updating notes for Mathcamp 2020 by `Apurva Nakade <https://apurvanakade.github.io>`__ and `Jalex Stark <https://jalexstark.com/>`__ 
with a lot of help from Mathcamp campers and Mathcamp staff Joanna and Maya.
Large chunks of these notes are taken from various learning resources available on the `leanprover-community website <https://leanprover-community.github.io/learn.html>`__.


Useful Links.
==================
#. `Formalizing 100 theorems <http://www.cs.ru.nl/~freek/100/index.html>`__
#. `Formalizing 100 theorems in Lean <https://leanprover-community.github.io/100.html>`__
#. Articles, videos, blog posts, etc. 
    #. `The Xena Project <https://xenaproject.wordpress.com/>`__
    #. `The Mechanization of Mathematics`_ 
    #. `The Future of Mathematics`_
    #. `Kevin Buzzard's Twitch channel <https://www.twitch.tv/kbuzzard>`__. In particular, checkout `this video <https://www.twitch.tv/videos/665779560>`__ about summer projects.
#. `Discord server <https://t.co/DSz6mbw4Oc?amp=1>`__ 
#. `Lean Zulip chat group`_


.. _`The Mechanization of Mathematics`: https://www.ams.org/journals/notices/201806/rnoti-p681.pdf
.. _`The Future of Mathematics`: https://www.youtube.com/watch?v=Dp-mQ3HxgDE
.. _`Lecture videos from LFTCM 2020`: https://www.youtube.com/playlist?list=PLlF-CfQhukNlxexiNJErGJd2dte_J1t1N
.. _Lean: https://leanprover.github.io/people/
.. _mathlib: https://leanprover-community.github.io/
.. _`Natural Number Game`: https://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/
.. _`mathlib repository`: https://github.com/leanprover-community/mathlib
.. _`Theorem Proving in Lean`: https://leanprover.github.io/theorem_proving_in_lean/
.. _`Lean Zulip chat group`: https://leanprover.zulipchat.com/
