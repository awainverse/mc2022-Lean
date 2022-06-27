.. _hint_1_mcsp:

Hint 1 for the math campers singing paradox
--------------------------------------------

Try 

.. code:: 
  
  cases em (∃ bob : camper, ¬ singing bob) with hyes hno,
  { cases hyes with bob key,
    sorry, },
  { sorry, }

Need more :doc:`hints <../hint_2_mcsp>`? 