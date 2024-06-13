

////////////////////////////////////////////////////////////
////////////////////// GAUDRY CODE /////////////////////////
////////////////////////////////////////////////////////////

/*
  File   : kummer.mag
  Purpose: Kummer surface arithmetic based on Theta functions
  Author : Pierrick Gaudry <gaudry@lix.polytechnique.fr>
  Licence: CeCILL version 2,    http://www.cecill.info/
           GPL version 2,       http://http://www.gnu.org/copyleft/gpl.html

  Comment:
    This sofware contains an implementation of the Kummer surface
    arithmetic described in the paper
      "Fast genus 2 arithmetic based on Theta functions"
    by P. Gaudry.
    Most of the formulae in that preprint are implemented here, with
    a view towards cryptography.
*/


//***********************
// Map from KS to Jac(C)
//***********************
// Formulae of Section 7.3
// This returns false if Genericity or Rationality condition fails.
function ThetaConstsFroma2b2c2d2(a2,b2,c2,d2)
  P := a2*d2 - b2*c2;
  S2 := a2^2 - b2^2 - c2^2 + d2^2 + 2*P;
  test, S := IsSquare(S2);
  if not test then return false, 0; end if;
  Delta := S2 - 4*P;
  test, sqDelta := IsSquare(Delta);
  if not test then return false, 0; end if;

  t52 := (S - sqDelta)/2;
  t62 := (S + sqDelta)/2;

  t74 := c2^2 - d2^2 + t52^2;
  test, t72 := IsSquare(t74);
  if not test then return false, 0; end if;
  if t72 eq 0 then return false, 0; end if;

  t82 :=  (a2*t52-d2*t62)/t72;
  t92 :=  (a2*c2-d2*b2)/t72;
  t102 := (b2*t52-c2*t62)/t72;

  sol := [a2, b2, c2, d2, t52, t62, t72, t82, t92, t102];
  for x in sol do
    if x eq 0 then
      return false, 0;
    end if;
  end for;

  return true, sol;
end function;

function ComputeThetaConstants(K)
  mus := K[2];
  //test, ThCst := ThetaConstsFroma2b2c2d2(KS`a^2, KS`b^2, KS`c^2, KS`d^2);
  test, ThCst := ThetaConstsFroma2b2c2d2(mus[1], mus[2], mus[3], mus[4]);
  if not test then
    error "Genericity or Rationality Condition is not verified";
  end if;
  return ThCst;
end function;

// Formulae of Section 7.4
//
// T1, T2, T3, T4: \theta_i(z)^2 for i in [1..4]
// t:  [ \theta_i(0)^2 : i in [1..10] ]
//
// Output: [ theta_i(z)^2 : i in [1..16] ]
function ThetaFromFundamentals(P, t)
  T1, T2, T3, T4 := Explode(P);
  T5 :=  ( -t[7]*t[8]*T1  + t[7]*t[10]*T2 + t[8]*t[9]*T3  - t[9]*t[10]*T4 ) / (t[9]^2-t[7]^2);
  T6 :=  (  t[9]*t[10]*T1 - t[8]*t[9]*T2  - t[7]*t[10]*T3 + t[7]*t[8]*T4  ) / (t[7]^2-t[9]^2);
  T7 :=  ( -t[5]*t[8]*T1  + t[5]*t[10]*T2 - t[6]*t[10]*T3 + t[6]*t[8]*T4  ) / (t[6]^2-t[5]^2);
  T8 :=  ( -t[5]*t[7]*T1  - t[6]*t[9]*T2  + t[5]*t[9]*T3  + t[6]*t[7]*T4  ) / (t[9]^2-t[7]^2);
  T9 :=  (  t[6]*t[10]*T1 - t[6]*t[8]*T2  + t[5]*t[8]*T3  - t[5]*t[10]*T4 ) / (t[8]^2-t[10]^2);
  T10 := (  t[6]*t[9]*T1  + t[5]*t[7]*T2  - t[6]*t[7]*T3  - t[5]*t[9]*T4  ) / (t[7]^2-t[9]^2);
  T11 := (  t[6]*t[8]*T1  - t[6]*t[10]*T2 + t[5]*t[10]*T3 - t[5]*t[8]*T4  ) / (t[6]^2-t[5]^2);
  T12 := ( -t[5]*t[10]*T1 + t[5]*t[8]*T2  - t[6]*t[8]*T3  + t[6]*t[10]*T4 ) / (t[8]^2-t[10]^2);
  T13 := ( -t[8]*t[9]*T1  + t[9]*t[10]*T2 + t[7]*t[8]*T3  - t[7]*t[10]*T4 ) / (t[7]^2-t[9]^2);
  T14 := ( -t[5]*t[9]*T1  - t[6]*t[7]*T2  + t[5]*t[7]*T3  + t[6]*t[9]*T4  ) / (t[7]^2-t[9]^2);
  T15 := ( -t[7]*t[10]*T1 + t[7]*t[8]*T2  + t[9]*t[10]*T3 - t[8]*t[9]*T4  ) / (t[7]^2-t[9]^2);
  T16 := ( -t[6]*t[7]*T1  - t[5]*t[9]*T2  + t[6]*t[9]*T3  + t[5]*t[7]*T4 )  / (t[7]^2-t[9]^2);

  return [T1,T2,T3,T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16];
end function;

function ThetaFromFundamentals_old(T1,T2,T3,T4, t)
  T5 :=  ( -t[7]*t[8]*T1  + t[7]*t[10]*T2 + t[8]*t[9]*T3  - t[9]*t[10]*T4 ) / (t[9]^2-t[7]^2);
  T6 :=  (  t[9]*t[10]*T1 - t[8]*t[9]*T2  - t[7]*t[10]*T3 + t[7]*t[8]*T4  ) / (t[7]^2-t[9]^2);
  T7 :=  ( -t[5]*t[8]*T1  + t[5]*t[10]*T2 - t[6]*t[10]*T3 + t[6]*t[8]*T4  ) / (t[6]^2-t[5]^2);
  T8 :=  ( -t[5]*t[7]*T1  - t[6]*t[9]*T2  + t[5]*t[9]*T3  + t[6]*t[7]*T4  ) / (t[9]^2-t[7]^2);
  T9 :=  (  t[6]*t[10]*T1 - t[6]*t[8]*T2  + t[5]*t[8]*T3  - t[5]*t[10]*T4 ) / (t[8]^2-t[10]^2);
  T10 := (  t[6]*t[9]*T1  + t[5]*t[7]*T2  - t[6]*t[7]*T3  - t[5]*t[9]*T4  ) / (t[7]^2-t[9]^2);
  T11 := (  t[6]*t[8]*T1  - t[6]*t[10]*T2 + t[5]*t[10]*T3 - t[5]*t[8]*T4  ) / (t[6]^2-t[5]^2);
  T12 := ( -t[5]*t[10]*T1 + t[5]*t[8]*T2  - t[6]*t[8]*T3  + t[6]*t[10]*T4 ) / (t[8]^2-t[10]^2);
  T13 := ( -t[8]*t[9]*T1  + t[9]*t[10]*T2 + t[7]*t[8]*T3  - t[7]*t[10]*T4 ) / (t[7]^2-t[9]^2);
  T14 := ( -t[5]*t[9]*T1  - t[6]*t[7]*T2  + t[5]*t[7]*T3  + t[6]*t[9]*T4  ) / (t[7]^2-t[9]^2);
  T15 := ( -t[7]*t[10]*T1 + t[7]*t[8]*T2  + t[9]*t[10]*T3 - t[8]*t[9]*T4  ) / (t[7]^2-t[9]^2);
  T16 := ( -t[6]*t[7]*T1  - t[5]*t[9]*T2  + t[6]*t[9]*T3  + t[5]*t[7]*T4 )  / (t[7]^2-t[9]^2);

  return [T1,T2,T3,T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16];
end function;

function RosenhainsFromGaudry(K, t)
  //notice this really only need t[8] and t[10] beyond what we have already
  //which are the zeroes of T[8] and T[10] and therefore feel a bit explicit
  l := t[1]*t[3]/t[2]/t[4];
  m := t[3]*t[8]/t[4]/t[10];
  n := t[1]*t[8]/t[2]/t[10];

  return l,m,n;
end function;

// Formulae of Section 4.3
function UfromZ(P, KS, T, t)
  assert OnKummer(P, KS);

  l := t[1]*t[3]/t[2]/t[4];
  m := t[3]*t[8]/t[4]/t[10];
  n := t[1]*t[8]/t[2]/t[10];


  U0 := l*T[14]*t[8]/(T[16]*t[10]);
  U1 := -(1-l)*T[13]*t[5]/(T[16]*t[10]);

  u0 := U0;
  u1 := (U1-U0-1);

  x := PolynomialRing(Parent(l)).1;
  return x^2 + u1*x + u0;
end function;

function KummerToRosenhain(P, K, ros)
  assert OnKummer(P, K);

  l := ros[1];
  m := ros[2];
  n := ros[3];
  // l := t[1]*t[3]/t[2]/t[4];
  // m := t[3]*t[8]/t[4]/t[10];
  // n := t[1]*t[8]/t[2]/t[10];
  t := ComputeThetaConstants(K);
  T := ThetaFromFundamentals(P, t);
  F := Parent(l);

  U0 := l*T[14]*t[8]/(T[16]*t[10]);
  U1 := -(1-l)*T[13]*t[5]/(T[16]*t[10]);

  u0 := F!U0;
  u1 := F!(U1-U0-1);

  x := PolynomialRing(F).1;
  return x^2 + u1*x + u0;
end function;

function U0U1(P, KS, T, t)
  assert OnKummer(P, KS);

  l := t[1]*t[3]/t[2]/t[4];
  m := t[3]*t[8]/t[4]/t[10];
  n := t[1]*t[8]/t[2]/t[10];


  U0 := l*T[14]*t[8]/(T[16]*t[10]);
  U1 := -(1-l)*T[13]*t[5]/(T[16]*t[10]);

  u0 := U0;
  u1 := (U1-U0-1);
  return u0, u1, l, m, n;
end function;

function U0U1_last(P, KS, T, t)
  assert OnKummer(P, KS);

  l := t[1]*t[3]/t[2]/t[4];
  m := t[3]*t[8]/t[4]/t[10];
  n := t[1]*t[8]/t[2]/t[10];


  U0 := l*T[14]*t[8]/(T[16]*t[10]);
  U1 := -(1-l)*T[13]*t[5]/(T[16]*t[10]);

  return U0, U1;
end function;

function DivFromU(U, J)
  return SetToSequence(Points(J, U, 2));
end function;

function V02FromZ(P, KS, T, t)
  den := (T[16]*t[2]*t[4]*t[10])^3;
  nnn := t[8]*t[3]^2*t[1]^2*T[14];

  abcd := KS`a*KS`b*KS`c*KS`d;

  coeff := (T[1]*T[3] + T[2]*T[4])*abcd -
    P[1]*P[2]*P[3]*P[4]*(t[1]*t[3] + t[2]*t[4]);

  num := T[12]*T[7]*t[2]*t[3]*t[9]^2 +  T[11]*T[9]*t[1]*t[4]*t[7]^2 +
    2*abcd*coeff;
  dd := nnn/den;
  return -num*dd;
end function;

function V02FromZ(P, K, T, t)
  den := (T[16]*t[2]*t[4]*t[10])^3;
  nnn := t[8]*t[3]^2*t[1]^2*T[14];

  abcd := &*K[2];

  coeff := (T[1]*T[3] + T[2]*T[4])*abcd -
    P[1]*P[2]*P[3]*P[4]*(t[1]*t[3] + t[2]*t[4]);

  num := T[12]*T[7]*t[2]*t[3]*t[9]^2 +  T[11]*T[9]*t[1]*t[4]*t[7]^2 +
    2*abcd*coeff;
  dd := nnn/den;
  return -num*dd;
end function;

function DivFromKSWeight1(P, KS)
  //C := CurveFromKS(KS);
  t := KS`SqThCst;
  T := ThetaFromFundamentals(P[1]^2, P[2]^2, P[3]^2, P[4]^2, t);

  assert T[16] eq 0;

  l := t[1]*t[3]/t[2]/t[4];
  m := t[3]*t[8]/t[4]/t[10];
  n := t[1]*t[8]/t[2]/t[10];


  U0 := l*T[14]*t[8];
  U1 := (l-1)*T[13]*t[5];

  den := U1 - U0;
  u0 := U0/den;

  f := HyperellipticPolynomials(C);
  test, v0 := IsSquare(Evaluate(f, -u0));
  if not test then
    error "Problem in DivFromKS: v0^2 has no square root!";
  end if;

  x := PolynomialRing(Parent(l)).1;
  return Jacobian(C)![x + u0, v0];
end function;


// Main function for the map K -> Jac(C)
//   It fails with an error if the point can not be mapped on the Jacobian of
//   the curve (but should be mapped on the quadratic twist).
function DivFromKS(P, KS)
  //C := CurveFromKS(KS);
  t := KS`SqThCst;
  T := ThetaFromFundamentals(P[1]^2, P[2]^2, P[3]^2, P[4]^2, t);

//   if T[16] eq 0 then
//     return DivFromKSWeight1(P, KS);
//   end if;

  U := UfromZ(P, KS, T, t);

  test, v0 := IsSquare(V02FromZ(P, KS, T, t));
  if not test then
    error "Problem in DivFromKS: v0^2 has no square root!";
  end if;

  Div := DivFromU(U, Jacobian(C));

  for D in Div do
    if Coefficient(D[2], 0) eq v0 then
      return D;
    end if;
  end for;
  error "not found in DivFromKS()";
end function;


////////////////////////////////////////////////////////////
/////////////////// END OF GAUDRY CODE /////////////////////
////////////////////////////////////////////////////////////
