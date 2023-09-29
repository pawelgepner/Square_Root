// C++ program to find out execution time of
// SQRT of functions

#include <chrono>
#include <functional>
#include <iomanip>
#include <iostream>
#include <algorithm>
#include <math.h>
#include "half.hpp"

using half = half_float::half;

// Porównać czas wykonania kodów i dokładność obliczeń kastomizowalnych funkcji sqrt z funkcją  biblioteczną sqrtf(x).

using namespace std::chrono;

const long int iterationsCount = 1000000;

#define FENV_SUPPORT 1

#ifdef __GNUC__
#define predict_true(x) __builtin_expect(!!(x), 1)
#define predict_false(x) __builtin_expect(x, 0)
#else
#define predict_true(x) (x)
#define predict_false(x) (x)
#endif

union asunit_u {float _f; uint32_t _i;};
union asfloat_u {uint32_t _i; float _f;};
union asuint64_u {double _f; uint64_t _i;};
union asdouble_u {uint64_t _i; double _f;};

#define asuint(f) ((asunit_u){f})._i
#define asfloat(i) ((asfloat_u){i})._f
#define asuint64(f) ((asuint64_u){f})._i
#define asdouble(i) ((asdouble_u){i})._f  

static inline uint32_t mul32(uint32_t a, uint32_t b)
{
	return (uint64_t)a*b >> 32;
}

/* returns a*b*2^-64 - e, with error 0 <= e < 3.  */
static inline uint64_t mul64(uint64_t a, uint64_t b)
{
	uint64_t ahi = a>>32;
	uint64_t alo = a&0xffffffff;
	uint64_t bhi = b>>32;
	uint64_t blo = b&0xffffffff;
	return ahi*bhi + (ahi*blo >> 32) + (alo*bhi >> 32);
}

float __math_invalidf(float x)
{
    return (x - x) / (x - x);
}

double __math_invalid(double x)
{
    return (x - x) / (x - x);
}

static inline double eval_as_double(double x)
{
    double y = x;
    return y;
}

const uint16_t __rsqrt_tab[128] = {
 0xb451,0xb2f0,0xb196,0xb044,0xaef9,0xadb6,0xac79,0xab43,
 0xaa14,0xa8eb,0xa7c8,0xa6aa,0xa592,0xa480,0xa373,0xa26b,
 0xa168,0xa06a,0x9f70,0x9e7b,0x9d8a,0x9c9d,0x9bb5,0x9ad1,
 0x99f0,0x9913,0x983a,0x9765,0x9693,0x95c4,0x94f8,0x9430,
 0x936b,0x92a9,0x91ea,0x912e,0x9075,0x8fbe,0x8f0a,0x8e59,
 0x8daa,0x8cfe,0x8c54,0x8bac,0x8b07,0x8a64,0x89c4,0x8925,
 0x8889,0x87ee,0x8756,0x86c0,0x862b,0x8599,0x8508,0x8479,
 0x83ec,0x8361,0x82d8,0x8250,0x81c9,0x8145,0x80c2,0x8040,
 0xff02,0xfd0e,0xfb25,0xf947,0xf773,0xf5aa,0xf3ea,0xf234,
 0xf087,0xeee3,0xed47,0xebb3,0xea27,0xe8a3,0xe727,0xe5b2,
 0xe443,0xe2dc,0xe17a,0xe020,0xdecb,0xdd7d,0xdc34,0xdaf1,
 0xd9b3,0xd87b,0xd748,0xd61a,0xd4f1,0xd3cd,0xd2ad,0xd192,
 0xd07b,0xcf69,0xce5b,0xcd51,0xcc4a,0xcb48,0xca4a,0xc94f,
 0xc858,0xc764,0xc674,0xc587,0xc49d,0xc3b7,0xc2d4,0xc1f4,
 0xc116,0xc03c,0xbf65,0xbe90,0xbdbe,0xbcef,0xbc23,0xbb59,
 0xba91,0xb9cc,0xb90a,0xb84a,0xb78c,0xb6d0,0xb617,0xb560,
 };

static inline float eval_as_float(float x)
 {
     float y = x;
     return y;
}

static	const double	one	= 1.0, tiny=1.0e-300;

#define __HI(x) *(1+(int*)&x)
#define __LO(x) *(int*)&x
#define __HIp(x) *(1+(int*)x)
#define __LOp(x) *(int*)x

double __ieee754_sqrt(double x)
{
	double z;
	int 	sign = (int)0x80000000; 
	unsigned r,t1,s1,ix1,q1;
	int ix0,s0,q,m,t,i;

	ix0 = __HI(x);			/* high word of x */
	ix1 = __LO(x);		/* low word of x */

    /* take care of Inf and NaN */
	if((ix0&0x7ff00000)==0x7ff00000) {			
	    return x*x+x;		/* sqrt(NaN)=NaN, sqrt(+inf)=+inf
					   sqrt(-inf)=sNaN */
	} 
    /* take care of zero */
	if(ix0<=0) {
	    if(((ix0&(~sign))|ix1)==0) return x;/* sqrt(+-0) = +-0 */
	    else if(ix0<0)
		return (x-x)/(x-x);		/* sqrt(-ve) = sNaN */
	}
    /* normalize x */
	m = (ix0>>20);
	if(m==0) {				/* subnormal x */
	    while(ix0==0) {
		m -= 21;
		ix0 |= (ix1>>11); ix1 <<= 21;
	    }
	    for(i=0;(ix0&0x00100000)==0;i++) ix0<<=1;
	    m -= i-1;
	    ix0 |= (ix1>>(32-i));
	    ix1 <<= i;
	}
	m -= 1023;	/* unbias exponent */
	ix0 = (ix0&0x000fffff)|0x00100000;
	if(m&1){	/* odd m, double x to make it even */
	    ix0 += ix0 + ((ix1&sign)>>31);
	    ix1 += ix1;
	}
	m >>= 1;	/* m = [m/2] */

    /* generate sqrt(x) bit by bit */
	ix0 += ix0 + ((ix1&sign)>>31);
	ix1 += ix1;
	q = q1 = s0 = s1 = 0;	/* [q,q1] = sqrt(x) */
	r = 0x00200000;		/* r = moving bit from right to left */

	while(r!=0) {
	    t = s0+r; 
	    if(t<=ix0) { 
		s0   = t+r; 
		ix0 -= t; 
		q   += r; 
	    }
	    ix0 += ix0 + ((ix1&sign)>>31);
	    ix1 += ix1;
	    r>>=1;
	}

	r = sign;
	while(r!=0) {
	    t1 = s1+r; 
	    t  = s0;
	    if((t<ix0)||((t==ix0)&&(t1<=ix1))) { 
		s1  = t1+r;
		if(((t1&sign)==sign)&&(s1&sign)==0) s0 += 1;
		ix0 -= t;
		if (ix1 < t1) ix0 -= 1;
		ix1 -= t1;
		q1  += r;
	    }
	    ix0 += ix0 + ((ix1&sign)>>31);
	    ix1 += ix1;
	    r>>=1;
	}

    /* use floating add to find out rounding direction */
	if((ix0|ix1)!=0) {
	    z = one-tiny; /* trigger inexact flag */
	    if (z>=one) {
	        z = one+tiny;
	        if (q1==(unsigned)0xffffffff) { q1=0; q += 1;}
		else if (z>one) {
		    if (q1==(unsigned)0xfffffffe) q+=1;
		    q1+=2; 
		} else
	            q1 += (q1&1);
	    }
	}
	ix0 = (q>>1)+0x3fe00000;
	ix1 =  q1>>1;
	if ((q&1)==1) ix1 |= sign;
	ix0 += (m <<20);
	__HI(z) = ix0;
	__LO(z) = ix1;
	return z;
}

/* see sqrt.c for more detailed comments.  */

inline float sqrtf_alt(float x)
{
	uint32_t ix, m, m1, m0, even, ey;

	ix = asuint(x);
	if (predict_false(ix - 0x00800000 >= 0x7f800000 - 0x00800000)) {
		/* x < 0x1p-126 or inf or nan.  */
		if (ix * 2 == 0)
			return x;
		if (ix == 0x7f800000)
			return x;
		if (ix > 0x7f800000)
			return __math_invalidf(x);
		/* x is subnormal, normalize it.  */
		ix = asuint(x * 0x1p23f);
		ix -= 23 << 23;
	}

	/* x = 4^e m; with int e and m in [1, 4).  */
	even = ix & 0x00800000;
	m1 = (ix << 8) | 0x80000000;
	m0 = (ix << 7) & 0x7fffffff;
	m = even ? m0 : m1;

	/* 2^e is the exponent part of the return value.  */
	ey = ix >> 1;
	ey += 0x3f800000 >> 1;
	ey &= 0x7f800000;

	/* compute r ~ 1/sqrt(m), s ~ sqrt(m) with 2 goldschmidt iterations.  */
	static const uint32_t three = 0xc0000000;
	uint32_t r, s, d, u, i;
	i = (ix >> 17) % 128;
	r = (uint32_t)__rsqrt_tab[i] << 16;
	/* |r*sqrt(m) - 1| < 0x1p-8 */
	s = mul32(m, r);
	/* |s/sqrt(m) - 1| < 0x1p-8 */
	d = mul32(s, r);
	u = three - d;
	r = mul32(r, u) << 1;
	/* |r*sqrt(m) - 1| < 0x1.7bp-16 */
	s = mul32(s, u) << 1;
	/* |s/sqrt(m) - 1| < 0x1.7bp-16 */
	d = mul32(s, r);
	u = three - d;
	s = mul32(s, u);
	/* -0x1.03p-28 < s/sqrt(m) - 1 < 0x1.fp-31 */
	s = (s - 1)>>6;
	/* s < sqrt(m) < s + 0x1.08p-23 */

	/* compute nearest rounded result.  */
	uint32_t d0, d1, d2;
	float y, t;
	d0 = (m << 16) - s*s;
	d1 = s - d0;
	d2 = d1 + s + 1;
	s += d1 >> 31;
	s &= 0x007fffff;
	s |= ey;
	y = asfloat(s);
	if (FENV_SUPPORT) {
		/* handle rounding and inexact exception. */
		uint32_t tiny = predict_false(d2==0) ? 0 : 0x01000000;
		tiny |= (d1^d2) & 0x80000000;
		t = asfloat(tiny);
		y = eval_as_float(y + t);
	}
	return y;
}

inline double sqrt_alt(double x)
{
	uint64_t ix, top, m;

	/* special case handling.  */
	ix = asuint64(x);
	top = ix >> 52;
	if (predict_false(top - 0x001 >= 0x7ff - 0x001)) {
		/* x < 0x1p-1022 or inf or nan.  */
		if (ix * 2 == 0)
			return x;
		if (ix == 0x7ff0000000000000)
			return x;
		if (ix > 0x7ff0000000000000)
			return __math_invalid(x);
		/* x is subnormal, normalize it.  */
		ix = asuint64(x * 0x1p52);
		top = ix >> 52;
		top -= 52;
	}

	/* argument reduction:
	   x = 4^e m; with integer e, and m in [1, 4)
	   m: fixed point representation [2.62]
	   2^e is the exponent part of the result.  */
	int even = top & 1;
	m = (ix << 11) | 0x8000000000000000;
	if (even) m >>= 1;
	top = (top + 0x3ff) >> 1;

	/* approximate r ~ 1/sqrt(m) and s ~ sqrt(m) when m in [1,4)

	   initial estimate:
	   7bit table lookup (1bit exponent and 6bit significand).

	   iterative approximation:
	   using 2 goldschmidt iterations with 32bit int arithmetics
	   and a final iteration with 64bit int arithmetics.

	   details:

	   the relative error (e = r0 sqrt(m)-1) of a linear estimate
	   (r0 = a m + b) is |e| < 0.085955 ~ 0x1.6p-4 at best,
	   a table lookup is faster and needs one less iteration
	   6 bit lookup table (128b) gives |e| < 0x1.f9p-8
	   7 bit lookup table (256b) gives |e| < 0x1.fdp-9
	   for single and double prec 6bit is enough but for quad
	   prec 7bit is needed (or modified iterations). to avoid
	   one more iteration >=13bit table would be needed (16k).

	   a newton-raphson iteration for r is
	     w = r*r
	     u = 3 - m*w
	     r = r*u/2
	   can use a goldschmidt iteration for s at the end or
	     s = m*r

	   first goldschmidt iteration is
	     s = m*r
	     u = 3 - s*r
	     r = r*u/2
	     s = s*u/2
	   next goldschmidt iteration is
	     u = 3 - s*r
	     r = r*u/2
	     s = s*u/2
	   and at the end r is not computed only s.

	   they use the same amount of operations and converge at the
	   same quadratic rate, i.e. if
	     r1 sqrt(m) - 1 = e, then
	     r2 sqrt(m) - 1 = -3/2 e^2 - 1/2 e^3
	   the advantage of goldschmidt is that the mul for s and r
	   are independent (computed in parallel), however it is not
	   "self synchronizing": it only uses the input m in the
	   first iteration so rounding errors accumulate. at the end
	   or when switching to larger precision arithmetics rounding
	   errors dominate so the first iteration should be used.

	   the fixed point representations are
	     m: 2.30 r: 0.32, s: 2.30, d: 2.30, u: 2.30, three: 2.30
	   and after switching to 64 bit
	     m: 2.62 r: 0.64, s: 2.62, d: 2.62, u: 2.62, three: 2.62  */

	static const uint64_t three = 0xc0000000;
	uint64_t r, s, d, u, i;

	i = (ix >> 46) % 128;
	r = (uint32_t)__rsqrt_tab[i] << 16;
	/* |r sqrt(m) - 1| < 0x1.fdp-9 */
	s = mul32(m>>32, r);
	/* |s/sqrt(m) - 1| < 0x1.fdp-9 */
	d = mul32(s, r);
	u = three - d;
	r = mul32(r, u) << 1;
	/* |r sqrt(m) - 1| < 0x1.7bp-16 */
	s = mul32(s, u) << 1;
	/* |s/sqrt(m) - 1| < 0x1.7bp-16 */
	d = mul32(s, r);
	u = three - d;
	r = mul32(r, u) << 1;
	/* |r sqrt(m) - 1| < 0x1.3704p-29 (measured worst-case) */
	r = r << 32;
	s = mul64(m, r);
	d = mul64(s, r);
	u = (three<<32) - d;
	s = mul64(s, u);  /* repr: 3.61 */
	/* -0x1p-57 < s - sqrt(m) < 0x1.8001p-61 */
	s = (s - 2) >> 9; /* repr: 12.52 */
	/* -0x1.09p-52 < s - sqrt(m) < -0x1.fffcp-63 */

	/* s < sqrt(m) < s + 0x1.09p-52,
	   compute nearest rounded result:
	   the nearest result to 52 bits is either s or s+0x1p-52,
	   we can decide by comparing (2^52 s + 0.5)^2 to 2^104 m.  */
	uint64_t d0, d1, d2;
	double y, t;
	d0 = (m << 42) - s*s;
	d1 = s - d0;
	d2 = d1 + s + 1;
	s += d1 >> 63;
	s &= 0x000fffffffffffff;
	s |= top << 52;
	y = asdouble(s);
	if (FENV_SUPPORT) {
		/* handle rounding modes and inexact exception:
		   only (s+1)^2 == 2^42 m case is exact otherwise
		   add a tiny value to cause the fenv effects.  */
		uint64_t tiny = predict_false(d2==0) ? 0 : 0x0010000000000000;
		tiny |= (d1^d2) & 0x8000000000000000;
		t = asdouble(tiny);
		y = eval_as_double(y + t);
	}
	return y;
}

inline float sqrt_approx(float& x)
{
    union { float y; uint32_t i; } val = {x};

    val.i -= 1 << 23;	/* Subtract 2^m. */
    val.i >>= 1;		/* Divide by 2. */
    val.i += 1 << 29;	/* Add ((b + 1) / 2) * 2^m. */
    return val.y;		/* Interpret again as float */
}

inline float sqrt_Newton(float& x)
{

    float l = 0.04f;
    float xx = x;
    float y;
    while (1) {
        y = 0.5f * (xx + (x / xx)); /* wzor Harona*/
        if (fabsf(y - xx) < l)
            break;
        xx = y;
    }
    return y;
}

inline float SQRT_P7 (float& x){
    int i=*(int*)&x;
    i=0x5f0b3892-(i>>1);
    float y=*(float*)&i;
    float c=x*y;
    y=c*(1.89099014875f - c*y);
    return y;
}

inline float SQRT_P22f ( float& x ) {
    float y , k0 , k1 , k2 ;
    u_int32_t i , i_mx , i_exp ;
    i = *( int *)& x ;
    i_exp = i & 0x7f800000 ;
    i_mx = (i & 0x00ffffff) ;
    if ( i_mx >= 0x00800000 ){
        i_exp = ( i_exp +0x3f800000 ) >> 1;
        k0 = -4668672.1917905799833277932902614932f ;
        k1 = 0.62946208956353013922056225279713351f ;
        k2 = - 0.86150539603051815126646385039843723e-8f ; // [1, 2) subinterval
    }
    else
    {
        i_exp = ( i_exp +0x3f000000 ) >>1;
        k0 = 3482322.9084655797566264144701179206f ;
        k1 = 0.68578878434790721561117673931552950f ;
        k2 = -0.12183586476093894040520123764728955e-7f  ; // [2, 4) subinterval
    }
    i_mx = k0 + ( k1 + k2 * i_mx ) * i_mx ;
    i_exp = i_exp | i_mx ;
    y = *( float *)& i_exp ;
    return y ;
}
inline float SQRT_P22int ( float& x ) {
    float y ;
    u_int32_t i , i_mx , i_exp , s = 23;
    i = *( int *)& x ;
    i_exp = i &0x7f800000 ;
    i_mx = i &0x00ffffff ;
    if ( i_mx >= 0x00800000 )
    {
        i_exp = ( i_exp +0x3f800000 ) >>1;
        i = 5280311 - ( int ) ((606231*( int64_t ) i_mx ) >> s );
        i = -4668672 + ( int ) (( i *( int64_t ) i_mx ) >> s );
    }
    else
    {
        i_exp = ( i_exp +0x3f000000 ) >>1;
        i = 5752813 - ( int ) ((857343*( int64_t ) i_mx ) >> s );
        i = 3482322 + ( int ) ( ( i *( int64_t ) i_mx ) >> s );
    }
    i = i_exp | i ;
    y = *( float *)& i ;
    return y ;
}

float Sqrt_linear_2parts_frexpf(float x)
{
    float  mx, y, k1, k0;
    int i_exp;
    mx = frexpf(x, &i_exp);
    if(i_exp % 2 == 0)
    {        k1 = 0.5901620670906446;
             k0 = 0.4173075996388651; // [1, 2) subinterval
             y = k1 * mx + k0;
             y = ldexpf(y, i_exp >>1);
    }
    else
    {
            k1 = 0.834615170955658;
            k0 = 0.5901620388031006; // [2, 4) subinterval
            y = k1 * mx + k0;
            y = ldexpf(y, (i_exp-1) >> 1);
    }
    return y;}



const float k0[2]={ -4668672.1917905799833277932902614932f, 3482322.9084655797566264144701179206f };

const float k1[2]={ 0.62946208956353013922056225279713351f , 0.68578878434790721561117673931552950f };

const float k2[2]={ - 0.86150539603051815126646385039843723e-8f, -0.12183586476093894040520123764728955e-7f };


float SQRT_P22f_1(float x)
{
    float y;
    u_int32_t  i, j, i_mx, i_exp;
    i = *(int*)&x;
    i_exp = i&0x7f800000;
    i_mx = i&0x00ffffff;
    if (i_mx>= 0x00800000)
    {	i_exp = (i_exp+0x3f800000)>>1;
        j=0;
    }
    else
    {	i_exp = (i_exp+0x3f000000)>>1;
        j=1;

    }
    i_mx = k0[j]+ i_mx*(k1[j]+ i_mx *k2[j]);
    i_exp = i_exp |i_mx;
    y = *(float*)&i_exp;
    return y;
}

const float kkk0[4]={ -4962991.5649160344616156702041546563, -4314840.5636832432756385094416406140, 3475637.6005081042619089300714104797, 3555060.6943003336688682855878979681};

const float kkk1[4]={ 0.68742852172973322187426350439952815, 0.57805617983979640427645651897907203, 0.70145434402552770375662264002628305,  0.65652595795543487851247398061009117};

const float kkk2[4]={ -0.11409842871220181827927592812361095e-7, -0.67843331661530860492524961502521342e-8, -0.16135954533025556512018646041775572e-7, -0.95944959752312947727186810335199900e-8};


float SQRT_P24f(float& x)
{
    float y;
    u_int32_t  i, j, i_mx, i_exp;
    i = *(int*)&x;
    i_exp = i&0x7f800000;
    i_mx = i&0x00ffffff;
    if (i_mx>= 0x00800000)
    {	i_exp = (i_exp+0x3f800000)>>1;
        if (i_mx >= 0x00b504f3)

        {j=1;}
        else
        {j=0;}
    }
    else
    {	i_exp = (i_exp+0x3f000000)>>1;
        if  (i_mx>= 0x003504f3)
        {j=3;}
        else
        {j=2;}

    }
    i_mx = kkk0[j]+ i_mx*(kkk1[j]+ i_mx *kkk2[j]);
    i_exp = i_exp |i_mx;
    y = *(float*)&i_exp;
    return y;
}


inline float SQRT_31f_one_iter (float& x)
{
    int i = *(int*)&x;
    int k = i & 0x00800000;
    float y;
    if (k != 0) {
        i = 0x5ed9e893 -(i >> 1);
        y = *(float*)&i;
        float c = x*y;
        y = 2.33130789f*c*fmaf(y, -c, 1.07495356f);
    } else {
        i = 0x5f19e8fd - (i >> 1);
        y = *(float*)&i;
        float c = x*y;
        y = 0.82421863f*c*fmaf(y, -c, 2.1499474f);
    }
    return y;
}
inline float SQRT_31f_two_iter (float& x)
{
    int i = *(int*)&x;
    int k = i & 0x00800000;
    float y;
    if (k != 0) {
        i = 0x5ed9e893 - (i >> 1);
        y = *(float*)&i;
        float c = x*y;
        y = 2.33130789f*y*fmaf(y, -c, 1.07495356f);
    } else {
        i = 0x5f19e8fd - (i >> 1);
        y = *(float*)&i;
        float c = x*y;
        y = 0.82421863f*y*fmaf(y, -c, 2.1499474f);
    }
    float c = x*y;
    float r = fmaf(y, -c, 1.0f);
    y = fmaf(0.5f*c, r, c);
    return y;
}






inline float SQRT_P42f ( float& x ){
    float y, k0, k1, k2, k3, k4;
    u_int32_t i, i_mx, i_exp;
    i = *( int *)& x ;
    i_exp = i &0x7f800000 ;
    i_mx = i &0x00ffffff ;
    if ( i_mx >= 0x00800000 ){
        i_exp = ( i_exp +0x3f800000 ) >>1;
        k0 = - 5671086.4827797608617542753432600037f ;
        k1 = + 0.91971194529690407659862360207886171f ;
        k2 = - 0.38325021634028297784255882461594555e-7f ;
        k3 = 0.12586920972031782800132549468525598e-14f ;
        k4 = -0.18188157092109794979119076853640167e-22f ; // [1, 2) subinterval
    }
    else
    {
        i_exp = ( i_exp +0x3f000000 ) >>1;
        k0=3474774.3905332614423102514814058249f;
        k1=+0.70639536668154512851480327208325990f;
        k2=-0.20263225962061877406272945119578003e-7f;
        k3=+0.91697440061687532236865407740721700e-15f;
        k4=-0.25721938434234066610403190133237333e-22f;  // [2, 4) subinterval

    }
    i_mx = k0 + i_mx *( k1 + i_mx *( k2 + i_mx *( k3 + k4 * i_mx )));
    i_exp = i_exp | i_mx ;
    y = *( float *)& i_exp ;
    return y ;
}


const float jk0[4]={ 2499016.0375455394108054244897629649f, 2717521.5172202391382457246567399963f, 3474678.3536506457929764539009103217f, 3480626.6021068235966198959344705742f };

const float jk1[4]={ 1.0029719106320466886080226972158298f, 0.91971194529690407659862360207886171f, 0.70705728461843137579702372467409730f,  0.70106270609105621764834916805633425f };

const float jk2[4]={ -0.50128647877689691560605578505073729e-7f,  -0.38325021634028297784255882461594555e-7f,
                     -0.20949491917739494118288571604376915e-7f, -0.18553104378034657053713579749294383e-7f };

const float jk3[4]={ 0.19968492972122162219068560441596961e-14f, 0.12586920972031782800132549468525598e-14f,
                     0.11451513516434266063480952189274380e-14f, 0.68821752178498594113073812547246888e-15f};

const float jk4[4]={ -0.35378486245280761264828987153451496e-22f, -0.18188157092109794979119076853640167e-22f,
                     -0.50032735064306049130618326143195035e-22f, -0.14874821130379719643459963684483170e-22f };



float SQRT_P44f(float& x)
{
    float y;
    u_int32_t  i, j, i_mx, i_exp;
    i = *(int*)&x;
    i_exp = i&0x7f800000;
    i_mx = i&0x00ffffff;
    if (i_mx>= 0x00800000)
    {	i_exp = (i_exp+0x3f800000)>>1;
        if (i_mx >= 0x00b504f3)

        {j=1;}
        else
        {j=0;}
    }
    else
    {	i_exp = (i_exp+0x3f000000)>>1;
        if  (i_mx>= 0x003504f3)
        {j=3;}
        else
        {j=2;}

    }
    i_mx = jk0[j]+ i_mx*(jk1[j]+ i_mx *(jk2[j]+ i_mx *(jk3[j]+ jk4[j]* i_mx)));
    i_exp = i_exp |i_mx;
    y = *(float*)&i_exp;
    return y;
}
const float hk0[4]={ -5889591.9624544605891945755102370351f, -5416760.3476449374067910174920666224f, 3474678.3536506457929764539009103217f, 3480626.6021068235966198959344705742f };

const float hk1[4]={ 1.0029719106320466886080226972158298f, 0.84339548425065700454217217144908044f, 0.70705728461843137579702372467409730f,  0.70106270609105621764834916805633425f };

const float hk2[4]={ -0.50128647877689691560605578505073729e-7f,  -0.29806672360807317180680432310813973e-7f,
                     -0.20949491917739494118288571604376915e-7f, -0.18553104378034657053713579749294383e-7f };

const float hk3[4]={ 0.19968492972122162219068560441596961e-14f, 0.83957170791382591107527060477671447e-15f,
                     0.11451513516434266063480952189274380e-14f, 0.68821752178498594113073812547246888e-15f};

const float hk4[4]={ -0.35378486245280761264828987153451496e-22f, -0.10518086890228445922547148690116953e-22f,
                     -0.50032735064306049130618326143195035e-22f, -0.14874821130379719643459963684483170e-22f };


const float gk0[4]={ -5889591.9624544605891945755102370351f, -5416760.3476449374067910174920666224f, 3474678.3536506457929764539009103217f, 3480626.6021068235966198959344705742f };

const float gk1[4]={ 1.0029719106320466886080226972158298f, 0.84339548425065700454217217144908044f, 0.70705728461843137579702372467409730f,  0.70106270609105621764834916805633425f };

const float gk2[4]={ -0.50128647877689691560605578505073729e-7f,  -0.29806672360807317180680432310813973e-7f,
                     -0.20949491917739494118288571604376915e-7f, -0.18553104378034657053713579749294383e-7f };

const float gk3[4]={ 0.19968492972122162219068560441596961e-14f, 0.83957170791382591107527060477671447e-15f,
                     0.11451513516434266063480952189274380e-14f, 0.68821752178498594113073812547246888e-15f};

const float gk4[4]={ -0.35378486245280761264828987153451496e-22f, -0.10518086890228445922547148690116953e-22f,
                     -0.50032735064306049130618326143195035e-22f, -0.14874821130379719643459963684483170e-22f };


float SQRT_P44f_2(float x)
{
    float y;
    u_int32_t  i, j, i_mx, i_exp;
    i = *(int*)&x;
    i_exp = i&0x7f800000;
    i_mx = i&0x00ffffff;
    if (i_mx>= 0x00800000)
    {	i_exp = (i_exp+0x3f800000)>>1;
        if (i_mx >= 0x00b504f3)

        {j=1;}
        else
        {j=0;}
    }
    else
    {	i_exp = (i_exp+0x3f000000)>>1;
        if  (i_mx>= 0x003504f3)
        {j=3;}
        else
        {j=2;}

    }
    i_mx = gk0[j]+ i_mx*(gk1[j]+ i_mx *(gk2[j]+ i_mx *(gk3[j]+ gk4[j]* i_mx)));
    i_exp = i_exp |i_mx;
    y = *(float*)&i_exp;
    return y;
}



const float ssk0[8]={ -5993856.4845583202543019157635409172, -5777112.9545990040547032721023002391,
                    -5540752.4591732058002190966126222114, -5282999.5112147815415160236732950879,
                    3474675.3018927213997242796185107800, 3474922.1590910115970702246315055407,
                    3477510.9327953865217808036653352564, 3487541.4989232080343478558091987281};

const float ssk1[8]={ 1.0473785059183161601102794826811175, +0.96045032469276359548137365005688549,
                     0.88073683104050350088298855633724331, 0.80763923506341109911631790641930693,
                     0.70710353086710318959504487692664849, 0.70655774248397872980933264558853321,
                     0.70368466711624833676983212377431295, 0.69678219478058145296786807132506023 };

const float ssk2[8]={ -0.57207001681740320004419536292539890e-7, -0.44112628641355098866109384255301003e-7,
                     -0.34015486713949109099958346218142791e-7, -0.26229525920886150109361569716941896e-7,
                     -0.21056359559366418665847240126362701e-7,  -0.20583736760380267159392498079439617e-7,
                     -0.19367434691098788949884844648174805e-7,  -0.17569547256782108730068178374985966e-7};

const float ssk3[8]={ 0.24973378828375540119560404667803433e-14,  0.16193232738960744500728835024443691e-14,
                     0.10500012366777000678805749783113706e-14,  0.68084156807805897604779639638476276e-15,
                     0.12244080102451566175221140661076936e-14,  0.10319713785583314253772922057478876e-14,
                     0.79894343210289166365754231546712097e-15,  0.58882073779048047972272588925788715e-15};

const float ssk4[8]={ -0.48623999233665347460846082729021660e-22, -0.26512423578710812008995454743014394e-22,
                     -0.14456001462140421968842954090131120e-22,-0.78821906889422005604812825601217535e-23,
                     -0.68764719173068514715588442144704801e-22 ,-0.37494228996393058788103991321709790e-22,
                     -0.20443873325444276867735011404427392e-22,-0.11147100973512989786511737825706394e-22};



float SQRT_P48f_1(float x)
{
    float y;
    u_int32_t  i, j, i_mx, i_exp;
    i = *(int*)&x;
    i_exp = i&0x7f800000;
    i_mx = i&0x00ffffff;
    if (i_mx>= 0x00800000)
    {	i_exp = (i_exp+0x3f800000)>>1;
        if (i_mx >= 0x00b504f3)
        {
            if (i_mx >= 0x00d744fd)	{j=3;}
            else 				{j=2;}
        }
        else
        {
            if (i_mx >= 0x009837f0) 	 {j=1;}
            else 				 {j=0;}
        }
    }
    else
    {	i_exp = (i_exp+0x3f000000)>>1;
        if  (i_mx>= 0x003504f3)
        {
            if  (i_mx>= 0x005744fd)		{j=7;}
            else 				{j=6;}
        }
        else
        {
            if (i_mx >= 0x001837f0)  	 {j=5;}
            else 				 {j=4;}
        }
    }
    i_mx = ssk0[j]+ i_mx*(ssk1[j]+ i_mx *(ssk2[j]+ i_mx *(ssk3[j]+ ssk4[j]* i_mx)));
    i_exp = i_exp |i_mx;
    y = *(float*)&i_exp;
    return y;
}


const double dk0[8]={-3217927197261939.3121151414393193886,
                    -3101563900662581.9011402435829460867,
                    -2974668825922561.7639273161982345973,
                    -2836288765681433.9940744734920955239,

                    1865452098231020.6640318905473328945,
                    1865584628680200.4871216680259612437,
                    1866974465979829.8713409679279014818,
                    1872359585164749.7153660606735290192};

const  double dk1[8]={ 1.0473785059183161601102794826811175,
                       0.96045032469276359548137365005688549,
                      0.88073683104050350088298855633724331,
                      0.80763923506341109911631790641930693,
                      0.70710353086710318959504487692664849,
                      0.70655774248397872980933264558853321,
                      0.70368466711624833676983212377431295,
                      0.69678219478058145296786807132506023 };

const double dk2[8]={ -0.10655634418454080820906820947777459e-15,
                     -0.82166173758646657441015139697680252e-16,
                     -0.63358781326467374525886673886594903e-16,
                     -0.48856299223166238720270934918787135e-16,
                     -0.3922052599371675153420723998241631e-16,
                     -0.38340197429769238753975365458875176e-16,
                     -0.36074658280422517936462247088877121e-16,
                     -0.32725831972029262650885020149845568e-16};

const double dk3[8]={ 0.86643813056090438344399045730177247e-32,
                     0.56181561968462830419543518280385871e-32,
                     0.36429235901389719477791970883273999e-32,
                     0.23621437031317408241075247884470474e-32,
                     0.42480186390926482406589297997473923e-32,
                     0.35803699538425722884760628505619860e-32,
                     0.27718918552927367936809185787025466e-32,
                     0.20428823139742607874297579727894651e-32};

const double dk4[8]={ -0.31422523024125976839842510879443343e-48,
                     -0.17133252168830737199654814373328285e-48,
                     -0.93419719879068577739616887856683890e-49,
                     -0.50937463455773286576909550765062978e-49,
                     -0.44438158224699797404561649722142256e-48,
                     -0.24230077584718673784271283283112151e-48,
                     -0.13211543484607421751473868871473538e-48,
                     -0.72036451652038484488244013046659932e-49};

float SQRT_P12i_1(float x){
    float y;
    int i;
    u_int32_t i_m, i_exp;
    int k1, k0;
    i = *(int*)&x;
    i_exp = i & 0x7f800000;
    i_m = i & 0x00ffffff;
    if(i_m>= 0x00800000)
    {
        i_exp = (i_exp+0x3f800000)>>1;
        k1=3500630;
        k0=-3437970; // [1, 2) subinterval
    }
    else
    {
        i_exp = (i_exp+0x3f000000)>>1;
        k1=4950638;
        k0=3563290; // [2, 4) subinterval
    }
    i_m = (int)(( k1* (int64_t)i_m)>> 23) + k0;
    i_exp |= i_m;
    y = *(float*)&i_exp;
    return y;
}

float SQRT_P12i_3(float x){
    float y;
    int i;
    u_int32_t i_m, i_exp;
    int k1, k0;
    i = *(int*)&x;
    i_exp = i & 0x7f800000;
    i_m = i & 0x00ffffff;
    if(i_m>= 0x00800000)
    {
        i_exp = (i_exp+0x3f800000)>>1;
        k1 =3500630;
        k0 =-3437970; // [1, 2) subinterval
    }else{
        i_exp = (i_exp+0x3f000000)>>1;
        k1 =4792612;
        k0 =3595995;  // [2, 4) subinterval
    }
    i_m = (int)(( k1* (int64_t)i_m)>> 23) + k0;
    i_exp |= i_m;
    y = *(float*)&i_exp;
    return y;
}

double SQRT_P48d(double x)
{
    double y;
    uint64_t  i, j, i_mx, i_exp;
    i = *(int64_t*)&x;
    i_exp = i & 0x7ff0000000000000;
    i_mx = i & 0x001fffffffffffff;;
    if (i_mx >= 0x0010000000000000)
    {
        // [1, 2) subinterval
        i_exp = (i_exp + 0x3ff0000000000000) >> 1;
        if (i_mx >= 0x0016a09e667f3bcc)
        {	if (i_mx >= 0x001ae89f995ad3ad) j = 3;
            else j = 2;
        }
        else
        {	if (i_mx >= 0x001306fe0a31b715) j = 1;
            else j = 0;
        }
    }
    else
    {
        // [2, 4) subinterval
        i_exp = (i_exp + 0x3fe0000000000000) >> 1;
        if (i_mx >= 0x0006a09e667f3bcc)
        {	if (i_mx >= 0x000ae89f995ad3ad) j = 7;
            else j = 6;
        }
        else
        {	if (i_mx >= 0x000306fe0a31b715) j = 5;
            else j = 4;
        }
    }
    i_mx = dk0[j]+ i_mx*(dk1[j]+ i_mx *(dk2[j]+ i_mx *(dk3[j]+ dk4[j]* i_mx)));
    i_exp = i_exp | i_mx;
    y = *(double*)  & i_exp;
    return y;
}

const int kkkk1[32] = {5842083, 5672603, 5517070, 5373672, 5240907, 5117522, 5002463, 4894832, 4793865, 4698899,4609363, 4524759, 4444650, 4368650, 4296421, 4221882, 4130977, 4011136, 3901158, 3799760, 3705881, 3618634, 3537275, 3461169, 3389774, 3322623, 3259312, 3199488, 3142842, 3089102, 3038029, 2989407};
const int kkkk0[32] = {3475356, 3485871, 3505245, 3532073, 3565213, 3603724, 3646831, 3693882, 3744333, 3797722, 3853655, 3911795, 3971855, 4033584, 4096766, 4166725,-4130495, -4003219, -3879542, -3759173, -3641861, -3527383, -3415543, -3306166, -3199097, -3094195, -2991333, -2890397,-2791282, -2693894, -2598144, -2503953};

float sqrt_P1_32int (float x)
{

    int i = *(int*)&x;
    int i_exp = i&0x7f800000;
    int i_mx = i&0x00ffffff;
    int j = i_mx>>19;
    i_mx = (int)((i_mx * (int64_t)kkkk1[j]) >> 23) + kkkk0[j];
    i_exp=(i_exp + 0x3f800000)>>1;
    i_exp = i_exp &0x7f800000;
    i_exp |= i_mx;
    float y = *(float *)&i_exp;
    return y;
}




const int32_t kk0[8]={ -5104762, -4807548,- 4483435,- 4129987, 3474795, 3485595, 3525015, 3607218};

const int32_t kk1[8]={ 6024011, 5524042, 5065569, 4645147, 5919451,5807466,5617954, 5377223 };

const int32_t kk2[8]={- 919163,-708771, -546537, -421438, -1299893, -1002354,- 772921, - 596003};

float SQRT_P28i_neq (float& x)
{
    float y;
    u_int32_t  i, j, i_mx, i_exp, s = 23;
    i = *(int*)&x;
    i_exp = i&0x7f800000;
    i_mx = i&0x00ffffff;
    if (i_mx>= 0x00800000)
    {	i_exp = (i_exp+0x3f800000)>>1;
        if (i_mx >= 0x00b504f3)
        {
            if (i_mx >= 0x00d744fd)	{j=3;}
            else 				{j=2;}
        }
        else
        {
            if (i_mx >= 0x009837f0) 	 {j=1;}
            else 				 {j=0;}
        }
    }
    else
    {	i_exp = (i_exp+0x3f000000)>>1;
        if  (i_mx>= 0x003504f3)
        {
            if  (i_mx>= 0x005744fd)		{j=7;}
            else 				{j=6;}
        }
        else
        {
            if (i_mx >= 0x001837f0)  	 {j=5;}
            else 				 {j=4;}
        }
    }
    i = kk1[j] + (int) ((kk2[j]*(int64_t) i_mx) >> s);
    i = kk0[j]+ (int) (( i*(int64_t) i_mx) >> s);
    i_exp = i_exp |i;
    y = *(float*)&i_exp;
    return y;
}

const float lk0[8]={ -5104762.5481843434072154644182911209, -4807548.9884504204695167341896345680,
                    - 4483435.4911616862349381343310706440 ,- 4129987.1817225059271193415881900721,
                    3474795.7036946603314064111686200687, 3485595.2163134391346538024000515077,
                    3525015.5713768604587921807767175214, 3607218.2922892895337836259513610476};

const float lk1[8]={ +0.71811812136345080369620487683352130, 0.65851719291216251043429364314869800,
                     0.60386293387988342145840978489932205, 0.55374475190960320655454537108613575,
                     0.70565356950701911208357819114149536,0.69230390238985349059708175762413646,
                     0.66971233981981169712518752598253062, 0.64101494956704250369088269019486738 };

const float lk2[8]={- 0.13062101278212073503567928721748766e-7,-0.10072255740618160981862643802889924e-7,
                    -0.77667711346715985809143320627154682e-8, -0.59889992611881903489733227103134153e-8,
                    -0.18472598987899986193170947447556576e-7, -0.14244321066278431965804262478932334e-7,
                    - 0.10983873074494728242407036754718526e-7, - 0.84697239802147849973818713454038307e-8};



inline float SQRT_P28f(float& x)
{

    float y;
    u_int32_t  i, j, i_mx, i_exp;
    i = *(int*)&x;
    i_exp = i&0x7f800000;
    i_mx = i&0x00ffffff;
    if (i_mx>= 0x00800000)
    {	i_exp = (i_exp+0x3f800000)>>1;
        if (i_mx >= 0x00b504f3)
        {
            if (i_mx >= 0x00d744fd)	{j=3;}
            else 				{j=2;}
        }
        else
        {
            if (i_mx >= 0x009837f0) 	 {j=1;}
            else 				 {j=0;}
        }
    }
    else
    {	i_exp = (i_exp+0x3f000000)>>1;
        if  (i_mx>= 0x003504f3)
        {
            if  (i_mx>= 0x005744fd)		{j=7;}
            else 				{j=6;}
        }
        else
        {
            if (i_mx >= 0x001837f0)  	 {j=5;}
            else 				 {j=4;}
        }
    }
    i_mx = lk0[j]+ i_mx*(lk1[j]+ i_mx *lk2[j]);
    i_exp = i_exp |i_mx;
    y = *(float*)&i_exp;
    return y;
}
float Sqrt_P2_32i_LIM(float x){
    float y;
    u_int32_t i_m, i_exp, s = 23;
    int32_t i, k0, k1,k2,k3;
    i = *(int*)&x;
    i_exp = i & 0x7f800000;
    i_m = i & 0x00ffffff;
    if(i_m>= 0x00800000)
    {
        i_exp = (i_exp+0x3f800000)>>1;
        k3=209190;
        k2=-1532998;
        k1 =6609579;
        k0 =-5285189; // [1, 2) subinterval
    }
            else
    {
        i_exp = (i_exp+0x3f000000)>>1;
        k3=286142;
        k2=-1268791;
        k1 =5895640;
        k0 =3475616; // [2, 4) subinterval
    }
    i = (int)(( k3* (int64_t)i_m)>> s) + k2;
    i = (int)(( i * (int64_t)i_m)>> s) + k1;
    i = (int)(( i * (int64_t)i_m)>> s) + k0;
    i_exp |= i;
    y = *(float*)&i_exp;
    return y;
}

float SQRT_P42i(float x)
{
    float y;
    uint32_t  i_mx, i_exp, s = 23;
    int32_t i, k0, k1,k2,k3,k4;
    i = *(int *) & x;
    i_exp = i&0x7f800000;
    i_mx = i&0x00ffffff;
    if (i_mx >= 0x00800000) {			// [1, 2) subinterval
        i_exp = (i_exp+0x3f800000)>>1;
        k0 = -5671087;
        k1 = 7715103;
        k2 = -2696884;
        k3 = 743001;
        k4 = -90063;
    }
    else {						        // [2, 4) subinterval
        i_exp = (i_exp+0x3f000000)>>1;
        k0 = 3474774;
        k1 = 5925674;
        k2 = -1425898;
        k3 = 541286;
        k4 = -127369;
    }

    i = (int)(( k4* (int64_t)i_mx)>> s) + k3;
    i = (int)(( i* (int64_t)i_mx)>> s) + k2;
    i = (int)(( i * (int64_t)i_mx)>> s) + k1;
    i = (int)(( i * (int64_t)i_mx)>> s) + k0;
    i_exp |= i;
    y = *(float*) & i_exp;
    return y;
}



const int32_t K2 [8] = {-1250736, -923677,-718064, -578908, -884405, -653137,-507747, -409354};
const int32_t K1[8] = {5911587, 5755208, 5553330, 5346755, 5948933, 5375819, 4942288, 4599442};
const int32_t K0[8] = {3474933, 3494031, 3543843, 3620683, -5064347, -4708996, -4385632, -4086848};

float sqrt_P2_28i_eq (float x)
{

    int i = *(int*)&x;
    int i_exp = i&0x7f800000;
    int i_m = i&0x00ffffff;
    int j = i_m>>21;
    i = (int)((i_m * (int64_t)K2[j]) >> 23) + K1[j];
    i = (int)((i_m * (int64_t)i) >> 23) + K0[j];
    i_exp=(i_exp + 0x3f800000)>>1;
    i_exp = i_exp &0x7f800000;
    i_exp |= i;
    float y = *(float *)&i_exp;
    return y;
}

const int32_t L3 [8] = {557952, 336695, 221336, 153567, 394530,
                        238089, 156501, 109316};
const int32_t L2 [8] = {-1456812, -1300896, -1132202, -981558, -2213710,
                        -1634149, -1270078, -1023880};
const int32_t L1[8]= {5930418, 5892136, 5809031, 5696866, 7437268, 6720406,
                      6178252, 5749695};
const int32_t L0[8] = {3474684, 3477962, 3491758, 3519733, -5618081,
                       -5322022, -5052593, -4803719};

float sqrt_P2_38i_eq (float x)
{
    int i = *(int*)&x;
    int i_exp = i&0x7f800000;
    int i_m = i&0x00ffffff;
    int j = i_m>>21;
    i = (int)((i_m * (int64_t)L3[j]) >> 23) + L2[j];
    i = (int)((i_m * (int64_t)i) >> 23) + L1[j];
    i = (int)((i_m * (int64_t)i) >> 23) + L0[j];
    i_exp=(i_exp + 0x3f800000)>>1;
    i_exp = i_exp &0x7f800000;
    i_exp |= i;
    float y = *(float *)&i_exp;
    return y;
}

const int32_t KK0[8]={ -5651877, -5404180, -5134067, -4839505, 3474678, 3476232, 3486022, 3514698};
const int32_t KK1[8]={ 7530662, 6905648, 6332507, 5806935, 5931061, 5908260, 5838723, 5714056};
const int32_t KK2[8]={ -2299578, -1773218, -1367337, -1054361, -1466808, -1350093, -1183087, -1001007 };
const int32_t KK3[8]={ 420796, 272853, 176923, 114720, 595096, 385872, 250207, 160862};


float SQRT_P38i_neq(float x)
{

    float y;
    uint32_t  j, i_mx, i_exp, s = 23;
    int32_t i;
    i = *(int*) & x;
    i_exp = i & 0x7f800000;
    i_mx = i & 0x00ffffff;
    if (i_mx >= 0x00800000) {   // [1, 2) segment
        i_exp = (i_exp + 0x3f800000) >> 1;
        if (i_mx >= 0x00b504f3) {
            if (i_mx >= 0x00d744fd) j = 3;
            else j = 2;
        }
        else {
            if (i_mx >= 0x009837f0) j = 1;
            else j = 0;
        }
    }
    else {                      // [2, 4) segment
        i_exp = (i_exp + 0x3f000000) >> 1;
        if (i_mx >= 0x003504f3) {
            if (i_mx >= 0x005744fd) j = 7;
            else j = 6;
        }
        else {
            if (i_mx >= 0x001837f0) j = 5;
            else j = 4;
        }
    }
    i = KK2[j] + (int32_t)((KK3[j] * (int64_t)i_mx) >> s);
    i = KK1[j] + (int32_t)((i * (int64_t)i_mx) >> s);
    i = KK0[j] + (int32_t)((i * (int64_t)i_mx) >> s);
    i_exp = i_exp | i;
    y = *(float*) & i_exp;
    return y;
}


float SQRT_P38i_eq (float x)
{

    const int32_t K3[8]={557952,336695,221336,
    153567, 394519, 238089, 156501, 109316};
    const int32_t K2[8]={-1456812, -1300896,
    -1132202,-981558,-2213672,-1634149,
    -1270078,-1023880};
    const int32_t K1[8]={5930418,5892136,5809031,
    5696866, 7437227, 6720406,6178252,5749695};
    const int32_t K0[8]={3474684,3477962,3491758,
    3519733,-5618066,-5322022,-5052593,-4803719};

    int i = *(int*)&x;
    int i_exp = i&0x7f800000;
    int i_m = i&0x00ffffff;
    int j = i_m>>21;
    i = (int)((K3[j]*(int64_t)i_m)>>23)+K2[j];
    i = (int)((i * (int64_t)i_m) >> 23) + K1[j];
    i = (int)((i * (int64_t)i_m) >> 23) + K0[j];
    i_exp=(i_exp + 0x3f800000)>>1;
    i_exp = i_exp &0x7f800000;
    i_exp |= i;
    float y = *(float *)&i_exp;
    return y;
}

const float LL0[8]={ -5993856.4845583202543019157635409172,
                    -5777112.9545990040547032721023002391, -5540752.4591732058002190966126222114,
                    -5282999.5112147815415160236732950879, 3474675.3018927213997242796185107800, 3474922.1590910115970702246315055407, 3477510.9327953865217808036653352564, 3487541.4989232080343478558091987281};

const float LL1[8]={ 1.0473785059183161601102794826811175, +0.96045032469276359548137365005688549, 0.88073683104050350088298855633724331, 0.80763923506341109911631790641930693, 0.70710353086710318959504487692664849, 0.70655774248397872980933264558853321, 0.70368466711624833676983212377431295, 0.69678219478058145296786807132506023 };

const float LL2[8]={ -0.57207001681740320004419536292539890e-7,
                     -0.44112628641355098866109384255301003e-7, -0.34015486713949109099958346218142791e-7,
                     -0.26229525920886150109361569716941896e-7, -0.21056359559366418665847240126362701e-7,
                     -0.20583736760380267159392498079439617e-7, -0.19367434691098788949884844648174805e-7,
                     -0.17569547256782108730068178374985966e-7};

const float LL3[8]={ 0.24973378828375540119560404667803433e-14,  0.16193232738960744500728835024443691e-14, 0.10500012366777000678805749783113706e-14,  0.68084156807805897604779639638476276e-15, 0.12244080102451566175221140661076936e-14,  0.10319713785583314253772922057478876e-14, 0.79894343210289166365754231546712097e-15,  0.58882073779048047972272588925788715e-15};

const float LL4[8]={ -0.48623999233665347460846082729021660e-22,
                     -0.26512423578710812008995454743014394e-22, -0.14456001462140421968842954090131120e-22,
                     -0.78821906889422005604812825601217535e-23, -0.68764719173068514715588442144704801e-22 ,
                     -0.37494228996393058788103991321709790e-22, -0.20443873325444276867735011404427392e-22,-0.11147100973512989786511737825706394e-22};



float SQRT_P48fd_neq(float x)
{
    float y;
    u_int32_t  i, j, i_mx, i_exp;
    i = *(int*)&x;
    i_exp = i&0x7f800000;
    i_mx = i&0x00ffffff;
    if (i_mx>= 0x00800000)
    {	i_exp = (i_exp+0x3f800000)>>1;
        if (i_mx >= 0x00b504f3)
        {
            if (i_mx >= 0x00d744fd)	{j=3;}
            else 				{j=2;}
        }
        else
        {
            if (i_mx >= 0x009837f0) 	 {j=1;}
            else 				 {j=0;}
        }
    }
    else
    {	i_exp = (i_exp+0x3f000000)>>1;
        if  (i_mx>= 0x003504f3)
        {
            if  (i_mx>= 0x005744fd)		{j=7;}
            else 				{j=6;}
        }
        else
        {
            if (i_mx >= 0x001837f0)  	 {j=5;}
            else 				 {j=4;}
        }
    }
    i_mx=fma(i_mx,fma(i_mx,fma(i_mx,fma(i_mx, LL4[j], LL3[j]), LL2[j]),LL1[j]),LL0[j]);
    i_exp = i_exp |i_mx;
    y = *(float*)&i_exp;
    return y;
}
const float W0[8]={ -5993856.4845583202543019157635409172,
                    -5777112.9545990040547032721023002391, -5540752.4591732058002190966126222114,
                    -5282999.5112147815415160236732950879, 3474675.3018927213997242796185107800, 3474922.1590910115970702246315055407, 3477510.9327953865217808036653352564, 3487541.4989232080343478558091987281};

const float W1[8]={ 1.0473785059183161601102794826811175, 0.96045032469276359548137365005688549, 0.88073683104050350088298855633724331, 0.80763923506341109911631790641930693, 0.70710353086710318959504487692664849, 0.70655774248397872980933264558853321, 0.70368466711624833676983212377431295, 0.69678219478058145296786807132506023 };

const float W2[8]={ -0.57207001681740320004419536292539890e-7,
                     -0.44112628641355098866109384255301003e-7, -0.34015486713949109099958346218142791e-7,
                     -0.26229525920886150109361569716941896e-7, -0.21056359559366418665847240126362701e-7,  -0.20583736760380267159392498079439617e-7, -0.19367434691098788949884844648174805e-7,  -0.17569547256782108730068178374985966e-7};

const float W3[8]={ 0.24973378828375540119560404667803433e-14,  0.16193232738960744500728835024443691e-14, 0.10500012366777000678805749783113706e-14,  0.68084156807805897604779639638476276e-15, 0.12244080102451566175221140661076936e-14,  0.10319713785583314253772922057478876e-14, 0.79894343210289166365754231546712097e-15,  0.58882073779048047972272588925788715e-15};

const float W4[8]={ -0.48623999233665347460846082729021660e-22,
                     -0.26512423578710812008995454743014394e-22, -0.14456001462140421968842954090131120e-22,
                     -0.78821906889422005604812825601217535e-23, -0.68764719173068514715588442144704801e-22 ,-0.37494228996393058788103991321709790e-22, -0.20443873325444276867735011404427392e-22,-0.11147100973512989786511737825706394e-22};



float SQRT_P48f_neq(float x)
{
    float y;
    u_int32_t  i, j, i_mx, i_exp;
    i = *(int*)&x;
    i_exp = i&0x7f800000;
    i_mx = i&0x00ffffff;
    if (i_mx>= 0x00800000)
    {	i_exp = (i_exp+0x3f800000)>>1;
        if (i_mx >= 0x00b504f3)
        {
            if (i_mx >= 0x00d744fd)	{j=3;}
            else 				{j=2;}
        }
        else
        {
            if (i_mx >= 0x009837f0) 	 {j=1;}
            else 				 {j=0;}
        }
    }
    else
    {	i_exp = (i_exp+0x3f000000)>>1;
        if  (i_mx>= 0x003504f3)
        {
            if  (i_mx>= 0x005744fd)		{j=7;}
            else 				{j=6;}
        }
        else
        {
            if (i_mx >= 0x001837f0)  	 {j=5;}
            else 				 {j=4;}
        }
    }
    i_mx=fmaf(i_mx,fmaf(i_mx,fmaf(i_mx,fmaf(i_mx, W4[j], W3[j]), W2[j]),W1[j]),W0[j]);
    i_exp = i_exp |i_mx;
    y = *(float*)&i_exp;
    return y;
}


const int32_t QK4[8] = {-311047, -153407, -85270, -51591,
                        -219944, -108475, -60295, -36480};
const int32_t QK3[8] = {711616, 566077, 434158, 334966,
                        1382963, 834177, 548178, 382778};
const int32_t QK2[8] = {-1480416, -1427119, -1330061,
                        -1219868, -3876037, -2860805, -2223255, -1792030};
const int32_t QK1[8]= {5931568, 5922400, 5890229,
                      5835499, 8677217, 7840750, 7208180, 6707969};
const int32_t QK0[8] = {3474676, 3475296, 3479349, 3489603,
                       -5964197, -5705206, -5469504, -5251679};


float sqrt_P48i_eq (float x)
{
    int i = *(int*)&x;
    int i_exp = i&0x7f800000;
    int i_m = i&0x00ffffff;
    int j = i_m>>21;
    i = (int)((QK4[j]*(int64_t)i_m) >> 23) + QK3[j];
    i = (int)((i * (int64_t)i_m) >> 23) + QK2[j];
    i = (int)((i * (int64_t)i_m) >> 23) + QK1[j];
    i = (int)((i * (int64_t)i_m) >> 23) + QK0[j];
    i_exp=(i_exp + 0x3f800000)>>1;
    i_exp = i_exp &0x7f800000;
    i_exp |= i;
    float y = *(float *)&i_exp;
    return y;
}

const int32_t WK0[8]={ -191803391, -184867597, -177304060,
                      -169055964, 111189625, 111197525, 111280366, 111601346};
const int32_t WK1[8]={ 281153527, 257818921, 236420993,
                      216799006, 189811659, 189665150, 188893914, 187041046};
const int32_t WK2[8]={ -128818715, -99332809, -76596067,
                      -59063642, -47414707, -46350455, -43611586, -39563103};
const int32_t WK3[8]={ 47173379, 30588152, 19833963, 12860734,
                      23128413, 19493388, 15091615, 11122509};
const int32_t WK4[8]={ -7704780, -4201061, -2290645, -1248983,
                      -10896205, -5941198, -3239461, -1766329};




float sqrt_P48i_neq (float x)
{

    float y;
    int32_t i;
    uint32_t   j, i_mx, i_exp;
    i = *(int*) & x;
    i_exp = i & 0x7f800000;
    i_mx = i & 0x00ffffff;
    if (i_mx >= 0x00800000)
    {
        // [1, 2) segment
        i_exp = (i_exp + 0x3f800000) >> 1;
        if (i_mx >= 0x00b504f3)
        {
            if (i_mx >= 0x00d744fd) j = 3;
            else j = 2;
        }
        else
        {
            if (i_mx >= 0x009837f0) j = 1;
            else j = 0;
        }
    }
    else
    {
        // [2, 4) segment
        i_exp = (i_exp + 0x3f000000) >> 1;
        if (i_mx >= 0x003504f3)
        {
            if (i_mx >= 0x005744fd) j = 7;
            else j = 6;
        }
        else
        {
            if (i_mx >= 0x001837f0) j = 5;
            else j = 4;
        }
    }
    i = (int)((WK4[j]*(int64_t)i_mx) >> 23) + WK3[j];
    i = (int)((i * (int64_t)i_mx) >> 23) + WK2[j];
    i = (int)((i * (int64_t)i_mx) >> 23) + WK1[j];
    i = (int)((i * (int64_t)i_mx) >> 23) + WK0[j];

    i=i >> 5;
    i_exp = i_exp | i;
    y = *(float*) & i_exp;
    return y;
}






static half y;
inline half* HALF_SQRT_P22int(half& x)
{
    u_int16_t  i, i_mx, i_exp, s = 10;
    i = *(int*)&x;
    i_exp = i&0x7c00;
    i_mx = i&0x07ff;
    if (i_mx>= 0x0400)
    {	i_exp = (i_exp+0x3c00)>>1;
        i = 645 - (int) ((74*(int32_t) i_mx) >> s);
        i = -570 + (int) (( i*(int32_t) i_mx) >> s);
    }
    else
    { 	i_exp = (i_exp+0x3800)>>1;
        i = 702 - (int) ((105*(int32_t) i_mx) >> s);
        i = 425 + (int) ( (i*(int32_t) i_mx) >> s);
    }
    i = i_exp |i;
    y = *(half *)&i;
    return &y;
}

inline half HALF_SQRT_P22int_wrap_for_rmsd(half& x)
{
    return *HALF_SQRT_P22int(x);
}

static __inline__ unsigned long long rdtsc(void) {
    unsigned hi, lo;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((unsigned long long)lo) | (((unsigned long long)hi) << 32);
}
/*********************************************************************************************************************/
template<class T, class F>
void profileExp(const std::string &desc, long int iterations, T& testVal, F func) {
    auto iter = iterations;
    while (iter--)
        func(testVal);
    iter = iterations;
    auto start = high_resolution_clock::now();
    while (iter--)
        func(testVal);
    auto stop = high_resolution_clock::now();
    auto time_eval = duration_cast<nanoseconds>(stop - start);
    std::cout << std::left << std::setw(45) << desc
              << time_eval.count() / iterations << " ns" << std::endl;
}

template<class T, class F>
void profileExpCycles(const std::string &desc, long int iterations, T &testVal, F func) {
    auto iter = iterations;
    while (iter--)
        func(testVal);
    iter = iterations;
    unsigned long long t = __builtin_readcyclecounter();
    while (iter--)
        func(testVal);
    t = __builtin_readcyclecounter() - t;
    std::cout << std::left << std::setw(45) << desc << t / (double)iterations
              << " cycles" << std::endl;
}

template<class T, class F>
void calculateExpRMSD(const std::string &desc, F func) {
    T currentValue = T(1.0f);
    T maxValue = T(4.f);
    int count = 0;
    long double RMSD = 0;

     long double  maxPoh = 0.0, maxValx = 0.0, maxValy = 0.0;
     long double  minPoh = 0.0, minValx = 0.0, minValy = 0.0;

    while (currentValue < maxValue) {
        currentValue = nextafterf(currentValue, maxValue);
        count++;

         long double ref = sqrtl( (long double)(currentValue));
         auto cal = func(currentValue);
        long double vidn = (long double)((long double)(cal) /(ref)) - 1;
        maxPoh = std::max(maxPoh, vidn);
        minPoh = std::min(minPoh, vidn);
        RMSD += std::pow(ref - cal, 2);
    }
    std::streamsize base = std::cout.precision();
    std::cout << std::left
        << std::setw(45) << desc
        << std::setw(17) << std::setprecision(base) << std::scientific << sqrtf(RMSD / count)
        << std::setw(16) << std::setprecision(4) << std::fixed << -log2(sqrtf(RMSD / count))
        << std::setw(17) << std::setprecision(base) << std::scientific << maxPoh
        << std::setw(17) << std::setprecision(base) << std::scientific << minPoh
        << std::setw(17) << std::setprecision(4) << std::fixed << -log2(std::max(abs(minPoh), maxPoh)) << std::endl;

}

template<class T, class F>
void calculateExpRMSD_half(const std::string &desc, F func) {
    T currentValue = T(1.0f);
    T maxValue = T(4.0f);
    int count = 0;
    double RMSD = 0;
    double maxPoh = 0.0, maxValx = 0.0, maxValy = 0.0;
    double minPoh = 0.0, minValx = 0.0, minValy = 0.0;

    while (currentValue < maxValue) {
        currentValue = half_float::nextafter(currentValue, maxValue);
        count++;

        auto ref = sqrt(double(currentValue));
        auto cal = func(currentValue);
        double vidn = (double)(double(cal) / (ref)) - 1;
        maxPoh = std::max(maxPoh, vidn);
        minPoh = std::min(minPoh, vidn);
        RMSD += std::pow(ref - cal, 2);
    }
    std::streamsize base = std::cout.precision();
    std::cout << std::left
        << std::setw(45) << desc
        << std::setw(17) << std::setprecision(base) << std::scientific << sqrtf(RMSD / count)
        << std::setw(16) << std::setprecision(4) << std::fixed << -log2(sqrtf(RMSD / count))
        << std::setw(17) << std::setprecision(base) << std::scientific << maxPoh
        << std::setw(17) << std::setprecision(base) << std::scientific << minPoh
        << std::setw(17) << std::setprecision(4) << std::fixed << -log2(std::max(abs(minPoh), maxPoh)) << std::endl;
}

int main() {
    float step = nextafterf(1.0f, 4.f)-1.0f ;
    half steph = half(step);

    std::cout << std::endl << "Step: " << step << " " << std::endl;

    std::cout << "Execution time:" << std::endl;


    profileExp("SQRT_P22f", iterationsCount, step, SQRT_P22f);

    profileExp("SQRT_P22int", iterationsCount, step, SQRT_P22int);
    profileExp("SQRT_P1_32int", iterationsCount, step, sqrt_P1_32int);
    profileExp("SQRT_P22half", iterationsCount, steph, HALF_SQRT_P22int);

    profileExp("SQRT_P42f", iterationsCount, step, SQRT_P42f);
    profileExp("SQRT_P28f", iterationsCount, step, SQRT_P28f);
    profileExp("SQRT_P28int", iterationsCount, step, SQRT_P28i_neq);
    profileExp("SQRT_P44f", iterationsCount, step, SQRT_P44f_2);
    profileExp("SQRT_P48f", iterationsCount, step, SQRT_P48f_1);
    profileExp("SQRT_P48d", iterationsCount, step, SQRT_P48d);
    profileExp("SQRT_P12i_1", iterationsCount, step, SQRT_P12i_1);
    profileExp("SQRT_P12i_3", iterationsCount, step, SQRT_P12i_3);
    profileExp("Sqrt_linear_2parts_frexpf", iterationsCount, step, Sqrt_linear_2parts_frexpf);
    profileExp("Sqrt_P2_32i_LIM", iterationsCount, step, Sqrt_P2_32i_LIM);
    profileExp("SQRT_P42i", iterationsCount, step, SQRT_P42i);
    profileExp("sqrt_P2_28i_eq", iterationsCount, step,  sqrt_P2_28i_eq);
    profileExp("sqrt_P2_38i_eq", iterationsCount, step,  sqrt_P2_38i_eq);
    profileExp("SQRT_P38i_neq", iterationsCount, step,  SQRT_P38i_neq);
    profileExp("SQRT_P38i_eq", iterationsCount, step,  SQRT_P38i_eq);
    profileExp("SQRT_P48fd_neq", iterationsCount, step,  SQRT_P48fd_neq);
    profileExp("SQRT_P48f_neq", iterationsCount, step,  SQRT_P48f_neq);
    profileExp("sqrt_P48i_eq", iterationsCount, step,  sqrt_P48i_eq);
    profileExp("sqrt_P48i_neq", iterationsCount, step,  sqrt_P48i_neq);

    profileExp("sqrt_alt", iterationsCount, step, sqrt_alt);
    profileExp("sqrtf_alt", iterationsCount, step, sqrtf_alt);
    profileExp("sqrt_sun", iterationsCount, step, __ieee754_sqrt);
    profileExp("std::sqrtf", iterationsCount, step, sqrtf);
    profileExp<float, float(float)>("std:::sqrt", iterationsCount, step, std::sqrt);


    std::cout << std::endl << "Number of cycles:" << std::endl;


    profileExpCycles("SQRT_P22f", iterationsCount, step, SQRT_P22f);

    profileExpCycles("SQRT_P22int", iterationsCount, step, SQRT_P22int);
    profileExpCycles("SQRT_P1_32int", iterationsCount, step, sqrt_P1_32int);
    profileExpCycles("SQRT_P22half", iterationsCount, steph, HALF_SQRT_P22int);

    profileExpCycles("SQRT_P42f", iterationsCount, step, SQRT_P42f);
    profileExpCycles("SQRT_P28f", iterationsCount, step, SQRT_P28f);
    profileExpCycles("SQRT_P28int", iterationsCount, step, SQRT_P28i_neq);
    profileExpCycles("SQRT_P44f", iterationsCount, step, SQRT_P44f_2);
    profileExpCycles("SQRT_P48f", iterationsCount, step, SQRT_P48f_1);
    profileExpCycles("SQRT_P48d", iterationsCount, step, SQRT_P48d);
    profileExpCycles("SQRT_P12i_1", iterationsCount, step, SQRT_P12i_1);
    profileExpCycles("SQRT_P12i_3", iterationsCount, step, SQRT_P12i_3);
    profileExpCycles("Sqrt_linear_2parts_frexpf", iterationsCount, step, Sqrt_linear_2parts_frexpf);
    profileExpCycles("Sqrt_P2_32i_LIM", iterationsCount, step, Sqrt_P2_32i_LIM);
    profileExpCycles("SQRT_P42i", iterationsCount, step, SQRT_P42i);
    profileExpCycles("sqrt_P2_28i_eq", iterationsCount, step, sqrt_P2_28i_eq);
    profileExpCycles("sqrt_P2_38i_eq", iterationsCount, step, sqrt_P2_38i_eq);
    profileExpCycles("SQRT_P38i_neq", iterationsCount, step, SQRT_P38i_neq);
    profileExpCycles("SQRT_P38i_eq", iterationsCount, step, SQRT_P38i_eq);
    profileExpCycles("SQRT_P48fd_neq", iterationsCount, step, SQRT_P48fd_neq);
    profileExpCycles("SQRT_P48f_neq", iterationsCount, step, SQRT_P48f_neq);
    profileExpCycles("sqrt_P48i_eq", iterationsCount, step, sqrt_P48i_eq);
    profileExpCycles("sqrt_P48i_neq", iterationsCount, step, sqrt_P48i_neq);

    profileExpCycles("sqrt_alt", iterationsCount, step, sqrt_alt);
    profileExpCycles("sqrtf_alt", iterationsCount, step, sqrtf_alt);
    profileExpCycles("sqrt_sun", iterationsCount, step, __ieee754_sqrt);
    profileExpCycles("std::sqrtf", iterationsCount, step, sqrtf);
    profileExpCycles<float, float(float)>("std::sqrt", iterationsCount, step, std::sqrt);

    std::cout << std::endl << std::left \
        << std::setw(45) << "NAZWA"
        << std::setw(17) << "RMSD" 
        << std::setw(17) << "BITY ZNACZĄCE"
        << std::setw(17) << "MAX REL ERROR"
        << std::setw(17) << "MIN REL ERROR"
        << std::setw(17) << "LICZBA BITOW OD MAX"
        << std::endl;


    calculateExpRMSD<float>("SQRT_P22f", SQRT_P22f);
    calculateExpRMSD<float>("SQRT_P22int", SQRT_P22int);
    calculateExpRMSD<float>("SQRT_P1_32int", sqrt_P1_32int);
    calculateExpRMSD_half<half>( "SQRT_P22half", HALF_SQRT_P22int_wrap_for_rmsd);
    calculateExpRMSD<float>("SQRT_P42f", SQRT_P42f);
    calculateExpRMSD<float>("SQRT_P28f", SQRT_P28f);
    calculateExpRMSD<float>("SQRT_P28int", SQRT_P28i_neq);
    calculateExpRMSD<float>("SQRT_P44", SQRT_P44f_2);
    calculateExpRMSD<float>("SQRT_P48f", SQRT_P48f_1);
    calculateExpRMSD<double>("SQRT_P48d", SQRT_P48d);
    calculateExpRMSD<double>("SQRT_P12i_1", SQRT_P12i_1);
    calculateExpRMSD<double>("SQRT_P12i_3", SQRT_P12i_3);
    calculateExpRMSD<double>("Sqrt_linear_2parts_frexpf", Sqrt_linear_2parts_frexpf);
    calculateExpRMSD<double>("Sqrt_P2_32i_LIM", Sqrt_P2_32i_LIM);
    calculateExpRMSD<double>("SQRT_P42i", SQRT_P42i);
    calculateExpRMSD<double>("sqrt_P2_28i_eq", sqrt_P2_28i_eq);
    calculateExpRMSD<double>("sqrt_P2_38i_eq", sqrt_P2_38i_eq);
    calculateExpRMSD<double>("SQRT_P38i_neq", SQRT_P38i_neq);
    calculateExpRMSD<double>("SQRT_P38i_eq", SQRT_P38i_eq);
    calculateExpRMSD<double>("SQRT_P48fd_neq", SQRT_P48fd_neq);
    calculateExpRMSD<double>("SQRT_P48f_neq", SQRT_P48f_neq);
    calculateExpRMSD<double>("sqrt_P48i_eq", sqrt_P48i_eq);
    calculateExpRMSD<double>("sqrt_P48i_neq", sqrt_P48i_neq);

    calculateExpRMSD<float>("sqrt_alt", sqrt_alt);
    calculateExpRMSD<float>("sqrtf_alt", sqrtf_alt);
    calculateExpRMSD<float>("sqrt_sun", __ieee754_sqrt);
    calculateExpRMSD<float>("std::sqrtf", sqrtf);
    calculateExpRMSD<float, float(float)>("std::::sqrt", std::sqrt);

    return 0;
}