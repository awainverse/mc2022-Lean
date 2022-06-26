.. _hint_2_mcsp:

Hint 2 for the math campers singing paradox
--------------------------------------------

Try 

.. code:: 
  
  cases em (∃ bob : camper, ¬ singing bob) with hyes hno,
  { cases hyes with bob key,
    use bob, },
  { push_neg at hno, -- a tactic from the glossary, which makes dealing with negations easier
    sorry, }
