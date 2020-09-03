# -*- coding: utf-8 -*-
"""
    Created on 09/03/2020
    Last Modification 09/03/2020
    
    @creator: Katharina BOUDGOUST
    
    ###############################################################################
    #   Public Key Encryption scheme based on Middle-Produc Learning with Errors  #
    ###############################################################################
    """

'''
This is a sage program realizing the Public Key Encryption (PKE) scheme from Roşca et al. [RSSS17].
The PKE scheme is chosen to be IND-CPA secure under the Middle-Product Learning With Errors (MP-LWE) problem using appropriate parameters.

The code consists of the following functions:

*polynomial_from_list*
This function takes as input a list of integers <list_a> and a modulus <q> and constructs a polynomial over <Z/qZ> whose coefficients correspond to <list_a>

*middle-product*
This function takes as input two polynomials <a> and <b> over the same ring.
The order of the middle-product is defined by <d>, i.e. we multiply <a> times <b> as polynomials and keep only the middle <d> coefficients for their middle-product. The number <k> specifies how many coefficients should be deleted below. For a more detailed introduction of the middle-product see Section 3.1 [RSSS17]

*setparams*
This function takes as input the security parameter <sec_lambda> and computes the parameters of the PKE scheme corresponding to the examples parameters given by the authors of [RSSS17] in Section 4.

*keygen*
This function computes a public key for the PKE scheme corresponding to the security parameter <sec_lambda>.

*encrypt*
This function takes as input the security parameter <sec_lambda> and computes the ciphertext <(c_1,c_2)> for the message <m> under the public key <pk>.

*decrypt*
This function takes as input the security parameter <sec_lambda> and decrypts the ciphertext <c> given the secret key <sk>.

References:
[RSSS17] Miruna Rosca and Amin Sakzad and Ron Steinfeld and Damien Stehle - Middle-Product Learning With Errors - https://eprint.iacr.org/2017/628
'''

# FUNCTION POLYNOMIAL_FROM_LIST
'''	INPUT: 	- list of integers <list_a> 
		- modulus <q>
	OUTPUT: - polynomial <tmp> over <Z/qZ> whose coefficients correspond to <list_a>

The list should start with the constant coefficient and end with the coefficient of the leading term.
The variable of the polynomial is 'x' 
'''
def polynomial_from_list(list_a,q):
	Z=ZZ.quotient(q) 
	P=PolynomialRing(Z,'x')
	x=P.gen()
	tmp=0 
	j=0
	for i in list_a: 
		tmp = tmp + (i * (x**(j))) 
		j += 1 
	return tmp

# FUNCTION MIDDLE-PRODUCT
''' 	INPUT:	- <a> and <b> : polynomials to middle-multiply
		- <d> : number of coefficients to preserve
		- <k> : number of coefficients to delete below and upper bound to delete on top
	OUTPUT: - The middle-product of <a> and <b> of width <d> over <Z/qZ>
'''
def middleproduct(a,b,d,k,q): 
	if a.parent() != b.parent():
		print("Oops, there is a problem: Your two polynomials don't have the same parent ring.")
	P=a.parent()	
	x=P.gen()
	# first compute the full product of a and b modulo x^(k+d) modulo q
	m=(a*b)%x^(k+d)
	# safe the coefficients
	m_list=m.list() 
	# deleting coefficients underneath
	for i in range(k):
		del m_list[0]         
	# rebuild the polynomial from the list	
	return polynomial_from_list(m_list,q)

# FUNCTION SETPARAMS
''' 	INPUT:	- <sec_lambda> : security parameter for the PKE scheme
	OUTPUT: - <n> : the dimension, should be even
		- <q> : the modulus, should be a prime
		- <t> : the number of MP-LWE samples
		- <alpha> : the width for the Gaussian distribution
		- <Z> : the quotient ring Z/qZ
		- <P> : the polynomial ring over <Z> in the variable <x>
		- <x> : the variable of <P>
'''
@cached_function
def setparams(sec_lambda):
	if sec_lambda%2 == 0:
		n=sec_lambda
	else: 
		n=sec_lambda+1
	q=next_prime(round(n^3*log(n)^(1/2)))
	t=round(log(n))
	alpha=0.001
	Z=ZZ.quotient(q) 
	P=PolynomialRing(Z,'x')
	x=P.gen()
	return (n,q,t,alpha,Z,P,x)

# FUNCTION KEYGEN
''' 	INPUT:	- <sec_lambda> : security parameter for the PKE scheme
	OUTPUT: - The secret key <sk> and the public key <pk> of the PKE scheme
'''
def keygen(sec_lambda):
	# initialize the parameters
	(n,q,t,alpha,Z,P,x)=setparams(sec_lambda)
	# initialize the public key tuple	
	pk=[]
	# sample private key
	s=P.random_element(2*n-2)
	sk=s
	for i in range(t):
		# choose <a> at random as the first part of public key
		a=P.random_element(n-1)
		# calculate the middle-product of <a> and <s>
		m=middleproduct(a,s,n,n-1,q)
		# register coefficients of this middle-product in a list
		list_m=m.list()
		# choose error polynomial
		# first sample coefficients
		list_e=[ZZ.random_element(x=alpha*q,distribution='gaussian') for k in range(n)]
		if len(list_m) != len(list_e):
			print("Oops, there is a problem: The dimensions of the middle-product and the error do not fit together.")
		# then add twice the error to the middle-product	
		for j in range(len(list_m)):
			list_m[j]=list_m[j]+2*list_e[j]
		# then add this MP-LWE sample to the public key
		pk.append((a,polynomial_from_list(list_m,q)))
	return (sk,pk)

# FUNCTION ENCRYPT
''' 	INPUT:	- <pk> : Public Key consisting of tuples (a_i,b_i)_{i <= t} 
		- <m> : message to encrypt as a list of <n/2> elements over {0,1}
		- <sec_lambda> : security parameter for the PKE scheme
	OUTPUT: - The ciphertext <(c_1,c_2)> of the message <m> under the public key <pk>
'''
def encrypt(pk,m,sec_lambda):
	# initialize the parameters
	(n,q,t,alpha,Z,P,x)=setparams(sec_lambda)
	# build message polynomial 
	m=polynomial_from_list(m,q)
	# set initial value of c_1 (first ciphertext part) and c_2 (second ciphertext part)
	c_1=0
	c_2=m
	for i in range(t):
		# choose random binary r
		list_r=[ZZ.random_element(0,2) for j in range(n/2+1)]
		r=polynomial_from_list(list_r,q)	
		c_1=c_1+r*pk[i][0]
		c_2=c_2+middleproduct(r,pk[i][1],n/2,n/2,q)
	return (c_1,c_2)

# FUNCTION DECRYPT
''' 	INPUT:	- <c> : Ciphertext computed via the function <encrypt> 
		- <sk> : Secret Key consisting of a polynomial of degree smaller than <2*n-1> 
		- <sec_lambda> : security parameter for the PKE scheme
	OUTPUT: - A list of binary integers. 
'''
def decrypt(c,sk,sec_lambda):
	# initialize the parameters
	(n,q,t,alpha,Z,P,x)=setparams(sec_lambda)
	result=c[1]-middleproduct(c[0],sk,n/2,((3*n)/2)-1,q)
	# centering the coefficients of result
	# in order to do so, translate it as a list of integers (not modulo q)
	coeff=result.list()
	for i in range(result.degree()+1):
		coeff[i]=Mod(coeff[i],q).lift_centered()%2
	return coeff

