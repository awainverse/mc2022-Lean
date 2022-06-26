.. _hint_2_barber_paradox:

Hint 2 for the barber paradox
-----------------------------------

Try

.. code:: 
  
    rintro h,
    cases h barber with h1 h2,
    cases em (shaves barber barber) with hyes hno,
    { sorry, },
    { sorry, } 