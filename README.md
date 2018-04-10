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

We use the program to calculate the Fourier expansion of the newform of level 11 and weight 2 at the cusp 0.
```
    sage: load('get_expansions.py')
    sage: f11 = Newforms(11)[0]
    sage: get_expansion(f11,mat=0,prec=2,verbose=False) #Set verbose to True for more information on the status of the calculation
    -1/11*q11 + 2/11*q11^2 + 1/11*q11^3 - 2/11*q11^4 - 1/11*q11^5 - 2/11*q11^6 + 2/11*q11^7 + 2/11*q11^9 + 2/11*q11^10 - 1/11*q11^11 + 2/11*q11^12 - 4/11*q11^13 - 4/11*q11^14 + 1/11*q11^15 + 4/11*q11^16 + 2/11*q11^17 - 4/11*q11^18 - 2/11*q11^20 - 2/11*q11^21 + O(q11^22)
```
Fourier expansions of newform of level 49 and weight 2. Note that we can also set a fractional precision:
```
    sage: f49 = Newforms(49,2)[0]
    sage: get_expansion(f49, prec = 13/49, mat = 0, verbose = False)
    -1/49*q49 - 1/49*q49^2 + 1/49*q49^4 + 3/49*q49^8 + 3/49*q49^9 - 4/49*q49^11 + O(q49^13)
```
