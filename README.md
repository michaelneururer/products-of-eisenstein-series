products-of-eisenstein-series
===========

Sage implementation of Eisenstein series and algorithm to compute Fourier expansions of modular forms at cusps.
Based on the article 'Products of Eisenstein series and Fourier expansions of modular forms at cusps' by Martin Dickson and Michalis Neururer.

The formulas used for the Fourier expansions of Eisenstein series are due to J. R. Weisinger 'Some results on classical Eisenstein series and modular forms over function fields' (these contain a few errors though) and unpublished notes of Henri Cohen.

Requirements
============

* Sage

Copyright
===========
Copyright (C) 2017 Martin Dickson, Michalis Neururer

products-of-eisenstein-series is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

products-of-eisenstein-series is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with modforms-db.  If not, see <http://www.gnu.org/licenses/>.

Example usage
==============

We use the program to calculate the Fourier expansion of the newform of level 11 and weight 2 at the cusp 1/11 (equivalent to i*infinity).

    sage: load('get_expansions.py')
    sage: f11 = Newforms(11)[0]
    sage: get_expansion(f11,cusp=1/11,prec=20,verbose=False)
    q1 - 2*q1^2 - q1^3 + 2*q1^4 + q1^5 + 2*q1^6 - 2*q1^7 - 2*q1^9 - 2*q1^10 + q1^11 - 2*q1^12 + 4*q1^13 + 4*q1^14 - q1^15 - 4*q1^16 - 2*q1^17 + 4*q1^18 + O(q1^20)
