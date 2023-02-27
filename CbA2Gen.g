
#Returns true if there exists a non-abelian cyclic-by-abelian finite p-group G such that inv(G)=L, and false otherwise.
IsInvariantVectorCbA2Gen := function(L)
    local  p,m,n1,n2,s1,s2,o1,o2,O1,O2,u1,u2, cond1,cond2,cond3,cond4,cond5,cond6,cond7,a1,a2;
    if Length(L)<>12 then
      return false;
    fi;
  p:=L[1];
  m:=L[2];
  n1:=L[3];
  n2:=L[4];
  s1:=L[5];
  s2:=L[6];
  o1:=L[7];
  o2:=L[8];
  O1:=L[9];
  O2:=L[10];
  u1:=L[11];
  u2:=L[12];
cond1:=IsPrime(p) and  n1>=n2 and n2>=1;
if not cond1 then
  return false;
fi;
cond2:= s1 in [-1,1] and s2 in [-1,1] and 0<= o1 and 0<= o2 and o1< Minimum(m,n1) and o2<Minimum(m,n2) and   RemInt(u1,p)<>0 and RemInt(u2,p)<>0;
if not cond2 then
  return false;
fi;
cond3:=(not (p=2 and m>=2)) or (o1<m-1 and o2< m-1);
if not cond3 then
  return false;
fi;
cond4:= 0<= o1 and 0 <= o2 and o1<=m-O1 and o2<=m-O2 and O1<= m-o2 ;
if not cond4 then
  return false;
fi;
cond5:= (o1=0) or (0<o1 and o1=o2 and s2=-1) or (o2=0 and 0<o1 and n2<n1) or (0<o2 and o2<o1 and o1<o2+n1-n2);
if not cond5 then
  return false;
fi;
a1:=Minimum(O1, o2+Minimum( n1-n2+O1-O2,0  ));
if o1=0 then
  a2:=0;
else if o2=0 then
    a2:=Minimum(o1,O2,O2-O1+Maximum(0,o1+n2-n1));
  else
    a2:=Minimum(o1-o2, O2-O1);
   fi;
fi;
cond6:= (not (s1=1)) or ((s2=1 and o2+O1 <=m and m<=n1 )  and
                         ((o1+O2<=m and m<=n2) or (2*m-o1-O2=n2 and n2<m and u2 mod p^(m-n2) =1) ) and
                         ( (not (o1=0))  or  (  (O1<=O2 and O2<=O1+o2+n1-n2 and Maximum(p-2,O2,n1-m)>0) or  (p=2 and m=n1 and O2=0 and O1=1) )  ) and
                         (  (not (o2=0 and 0<o1)) or  (O1+Minimum(0,n1-n2-o1)<=O2 and O2<=O1+n1-n2 and Maximum(p-2,O1,n1-m)>0) )       and
                         (    (not (0<o2 and o2<o1)) or (O1<=O2 and O2<=O1+n1-n2)      ) and
                         (1<=u1 and u1<=p^a1 ) and
                         (  (1<=u2 and u2<=p^a2)  or (o1*o2>0 and n1-n2+O1-O2=0 and 0<a1 and 1+p^a2<=u2 and u2<=2*p^a2 and u1 mod p =1   ))
                         );
if not cond6 then
    return false;
 fi;
cond7:= (not (s1=-1)) or ( (p=2 and m>=2 and O1<=1 and u1=1) and
                            ((not s2=1) or ( n2<n1 and    ( (not m<=n2) or (O2<=1 and u2=1 and (O1<=O2 or (o2=0 and 0<n1-n2 and n1-n2<o1))   )) and
                                                          ((not m>n2) or   m+1=n2+O2 and u2*(1+2^(m-o1-1)) mod p^(m-n2)= -1 mod p^(m-n2) and  1<=u2 and u2<=2^(m-n2+1) and (O1=1 or o1+1<>n1) and
                                                                       ( (O1=0 and  (o1=0 or o2+1<>n2)  )  or   (O1=1 and o2=0 and n1-n2<o1)   or  (u2<= 2^(m-n2)))
                                                            )
                                           )
                            ) and
                            (  (not s2=-1) or ( O2<=1 and u2=1 and (   (   (not (o1<=o2 and n1>n2)) or  (O1<=O2)  )
                                                                        or   (  (not  (o1=o2 and n1=n2)) or  (O1>=O2)  )
                                                                        or    (  (not ( o2=0 and 0<o1 and o1=n1-1 and n2=1)   ) or  (O1=1 or O2=1)  )
                                                                         or     (  (  not  (o2=0 and 0<o1 and  ( n1<>o1+1 or n2<>1   ) ))   or   (O1+Minimum(0,n1-n2-o1)<=O2)    )
                                                                          or   (   (not  (o1*o2>0 and o1<>o2)) or (O1<=O2)     )  )  )  )
      );
return cond7;
end;


#Creates the list of groups with initial parameters (p,m,n_1,n_2,1), i.e., with sigma_1=1.
A:=function(p,m,n1,n2)
	local o1,o2,O1,O2,u1,u2,list, CondicionOes, CondicionOprimas, CondicionOOprima,a1,a2,A1;
	list:=[];
  if   n1<n2 or (p>2 and n1<m ) or Minimum(n1,n2,m)<=0 then
    return list;
  else
	   o1:=0;
	    while  o1<m  and  (p>2 or m=1 or o1<m-1)  do
		      o2:=0;
		        while o2<Minimum(m ,n2) and (p>2 or m=1 or o2<m-1) do
			           CondicionOes:=(o1=0 and m<= n2) or (o2=0 and o1>0 and n2<n1) or (0<Minimum(o1,o2) and o2<o1 and o1-o2<n1-n2);
			              O1:=0;
			                 while CondicionOes and O1<= m-o1  do
				                     O2:=0;
					                        while O2<=  m-o2   do
						                              CondicionOprimas:=(  o1=0 and ((O1<= O2 and O2<=O1+o2+n1-n2   and ( p>2 or O2>0 or m<n1))  or  (p=2 and m=n1 and O2=0 and O1=1))) or
							                                               ( o1>0 and o2=0 and ((O1+Minimum(0,n1-n2-o1) <=O2 and   O2<= O1 +n1-n2 and (p>2 or O1>0 or m<n1)) or (p=2 and m=n1 and O1=0 and O2=m-n2+1)) ) or
							                                               (0<Minimum(o1,o2) and O1<=O2 and  O2<= O1+n1-n2);
						                               CondicionOOprima:= m<=2*m-o2-O1 and (m<=Minimum(n2,2*m-o1-O2) or n2=2*m-o1-O2);

                                           if o1=0 then
                                             a1:=Minimum(O1,o2+Minimum(0,n1-n2+O1-O2));
                                             a2:=0;
                                           fi;
                                           if o2=0 and 0<o1 then
                                              a1:=0;
                                              a2:=Minimum(o1,O2, O2-O1-Minimum(0,n1-n2-o1));
                                           fi;
                                           if 0<Minimum(o1,o2) then
                                              a1:=Minimum(o2,O1);
                                              a2 :=Minimum(o1-o2,O2-O1);
                                           fi;
                                           A1:=Minimum(n1-n2-o1+o2,n1-n2+O1-O2);
						                               u1:=1;
						                               while CondicionOprimas and CondicionOOprima and u1<=p^a1 do
							                                      if Gcd(u1,p)=1  then
  								                                         if 0<Minimum(o1,o2) and A1=0 and 0<a1 and 1=u1 mod p  then
									                                            u2:=1+p^a2;
									                                            while    u2<=2*p^a2 do
										                                              if (m<=n2 or 1=u2 mod p^( m-n2 )) and Gcd(u2,p)=1 then
											                                                  Add(list,  [p,m,n1,n2,1,1,o1,o2,O1,O2,u1,u2]  );
										                                              fi;
										                                          u2:=u2+1;
									                                           od;
                                                           fi;
									                                         u2:=1;
									                                         while u2<=p^a2 do
										                                          if (m<=n2 or 1=u2 mod p^( m-n2 )) and Gcd(u2,p)=1 then
											                                          Add(list , [ p,m,n1,n2,1,1,o1,o2,O1,O2,u1,u2 ]);
										                                          fi;
										                                          u2:=u2+1;
									                                         od;
								                                  fi;
							                                    u1:=u1+1;
						                              od;
                                          O2:=O2+1;
						                od;
			                    	O1:=O1+1;
			            od;
			           o2:=o2+1;
		       od;
           o1:=o1+1;
	    od;
    fi;
	    return list;
end;

#Creates the list of groups with initial parameters (p,m,n_1,n_2,-1), i.e., with sigma_1=-1.
B:=function(p,m,n1,n2)
	local s2,o1,o2,O1,O2,  u2,list, CondicionOes, CondicionOprimas ,   CondicionOOprima , t, a1,a2,A1;
	list:=[];
  if  p<>2 or  n1<n2 or   Minimum(n1,n2,m)<=0 then
    return list;
  else
    for s2 in [-1,1] do
      if n2<n1 or s2=-1 then
	      o1:=0;
	      while  o1<Minimum(m-1,n1)    do
		      o2:=0;
		        while o2<Minimum(m-1, n2)  do
			           CondicionOes:=(o1=0  ) or (0<o1 and o1=o2 and s2=-1) or (o2=0 and o1>0 and n2<n1) or (0<Minimum(o1,o2) and o2<o1 and o1-o2<n1-n2);
			              O1:=0;
			                 while CondicionOes and O1<=1  do
				                     O2:=0;
                             if s2=1 and m<=n2 then
                                while O2<=1 do
                                  if   (O1<=O2 or  (o2=0 and 0<n1-n2 and n1-n2<o1)) then
                                    Add(list,  [p,m,n1,n2,-1,s2,o1,o2,O1,O2,1,1]  );
                                  fi;
                                  O2:=O2+1;
                                od;
                             fi;
                             if s2=1 and n2<m  and (O1=1 or n1<>o1+1)    then
                                O2:=m-n2+1;
                                t:= (-1-2^(m-o1-1))^-1 mod 2^(m-n2 );
                                Add(list,  [p,m,n1,n2,-1,s2,o1,o2,O1,O2,1, t ]  );
                                if (O1=0 and (o2+1<n2 or o1=0)) or (O1=1 and o2=0 and n1-n2<o1) then
                                   Add(list,  [p,m,n1,n2,-1,s2,o1,o2,O1,O2,1, t+2^(m-n2) ]  );
                                fi;
                            fi;
                            if s2=-1 then
                              while O2<=1 do
                                CondicionOprimas:=  (not (o1=0 and n2<n1) or O1<=O2)
                                                and (not (0<o1 and o1=o2 and n2<n1) or (O1<=O2) )
                                                and (not (o1=o2 and n1=n2) or (O1>= O2) )
                                                and (not (o2=0 and 0<o1 and o1=n1-1 and n2=1) or (Maximum(O1,O2)=1 ))
                                                and (not (o2=0 and 0<o1 and  not (o1=n1-1 and n2=1) ) or ( O1+Minimum(0,n1-n2-o1)<=O2) )
                                                and (not (0<Minimum(o1,o2) and o1<>o2) or (O1 <=O2 ) )   ;
                                if   CondicionOprimas then
                                  Add(list,  [p,m,n1,n2,-1,s2,o1,o2,O1,O2,1,1]  );
                                fi;
                                O2:=O2+1;
                              od;
                           fi;
                           O1:=O1+1;
                      od;
                      o2:=o2+1;
                od;
                o1:=o1+1;
            od;
          fi;
          od;
        fi;
      return list;
  end;


#Creates the list of vector invariants of group of the given order.
  CbA2GenByOrder:=function(p, logorder )
           local m,n1,n2,list;
           list:=[];
           for m in [1..logorder-2] do
             for n1 in [1..logorder-m-1] do
               n2:=logorder -m-n1;
               if 1<=n2 then
                  Append(list, A(p,m,n1,n2));
                  Append(list, B(p,m,n1,n2));
               fi;
             od;
           od;
         return list;
   end;



   #######################################################


#Just compute S(r|n) mod p^m. It can be improved.
Ese:=function(r,n,p,m)
  local S,i,ri,M;
  S:=0;
  ri:=1;
  M:=p^m;
    if  (r mod p=1 and (p>2 or r mod 4=1) and PValuation(n,p)>=m) or ( p=2 and RemInt(n,p)=0 and r mod 4=3 and PValuation(n,p)+PValuation(r+1,p)-1>=m) then
     return 0;
  else
  for i in [0..n-1] do
    S:=S+ri mod M;
    ri:=ri*r mod M;
  od;
  return S mod M;
 fi;
end;





#This function creates directly the group as a pcp-group.
CbA2GenPcp:= function(L)
  local p,m,n1,n2,s1,s2,o1,o2,O1,O2,u1,u2,r1,r2,t1,t2,a,b, N,LL,F,FF, exponent, pvalexponent, pprimeexponent, col,i,j;
  if  not(IsInvariantVectorCbA2Gen(L) ) then
    Print("No se satisfacen las condiciones");
    return fail;
  else
    #Setting the Parameters
  p:=L[1];
  m:=L[2];
  n1:=L[3];
  n2:=L[4];
  s1:=L[5];
  s2:=L[6];
  o1:=L[7];
  o2:=L[8];
  O1:=L[9];
  O2:=L[10];
  u1:=L[11];
  u2:=L[12];
    r1:=s1*(1+ p^(m-o1)) mod p^m;
    if Minimum(o1,o2)=0 then
      r2:=s2*(1+p^(m-o2)) mod p^m;
    else
      r2:= s2*(1+p^(m-o1))^(p^(o1-o2)) mod p^m;
    fi;
fi;
  ###########################################################33
#Writting a pcp presentation.
LL:=[];
FF:=[];
N:=n1+n2+m;
 F := FreeGroup(IsSyllableWordsFamily, N);;
 FF:=MinimalGeneratingSet(F);
 for i in [1..N] do
   Add(LL, p);
 od;
 col := SingleCollector( F,LL );
 #We set f1=b1, f2=b1^p, ... f{n_1+1}=b1^(p^n1)
 for i in [1..n1-1] do
    SetPower( col, i, FF[i+1] );
od;
if 0<O1 then
  SetPower( col, n1, FF[n1+n2+1+m-O1]^u1 );
fi;
for i in [n1+1..n1+n2-1] do
  SetPower( col, i, FF[i+1] );
od;
if 0<O2  then
  SetPower( col, n1+n2, FF[n1+n2+1+m-O2]^u2 );
fi;
for i in [n1+n2+1..n1+n2+m-1] do
  SetPower( col, i, FF[i+1] );
od;

for i in [1..n1] do
   for j in [n1+1..n1+n2] do
       exponent:=Ese(r1,p^(i-1),p,m)*Ese( r2,p^(j-n1-1),p,m) mod p^m;
       pvalexponent:=PValuation(exponent,p);
       if pvalexponent<m then
       pprimeexponent:=exponent/p^pvalexponent;
       SetConjugate( col, j, i, FF[j]*FF[n1+n2+1+pvalexponent]^pprimeexponent );
     fi;
   od;
   for j in [n1+n2+1.. n1+n2+m] do
     exponent:=(r1^(p^(i-1))-1)* p^(j-n1-n2-1) mod p^m;
     pvalexponent:=PValuation(exponent,p);
     if pvalexponent<m then
     pprimeexponent:=exponent/p^pvalexponent;
   SetConjugate( col, j, i, FF[j]*FF[n1+n2+1+pvalexponent]^pprimeexponent );
    fi;
   od;
od;

for i in [n1+1..n1+n2] do
   for j in [n1+n2+1.. n1+n2+m] do
     exponent:=(r2^(p^(i-n1-1))-1)*p^(j-n1-n2-1) mod p^m;
     pvalexponent:=PValuation(exponent,p);
     if pvalexponent<m then
     pprimeexponent:=exponent/p^pvalexponent;
     SetConjugate( col, j, i, FF[j]*FF[n1+n2+1+pvalexponent]^pprimeexponent );
      fi;
   od;
od;
return GroupByRws( col );
end;


#Returns a list whose first entry is the list of parameters of G, and the second one is an optimal basis [b1,b2] for G.
InvariantsAndBasis:=function(G)
local G2, InvG2,InvGAb,N,Fact,p,m,n1,n2,GAb,BAb,bb1,bb2,c,a4,x,d,q,c2,d2,e,b1,b2,a,s1,s2,o1,o2,o,O1,O2,
u1,u2,uu1,uu2,r1,r2,OO1,OO2,x1,x2,y1,y2,a1,a2,r,R,R1,R2,rprime,R1prime,R2prime,Rprime,delta,q1,q2,a1prime,pa1,pa2,
apmO1,apmO2,b1pn1,b2pn2,aa,ar1,ar2,y,b1p,b2p,Divisors;

# To compute  p, m, n1 y n2

G2 := DerivedSubgroup(G);
InvG2 := AbelianInvariants(G2);
e:=NaturalHomomorphismByNormalSubgroup(G,G2);
GAb:=Image(e);
InvGAb:=AbelianInvariants(GAb);
N:=Size(G);
Divisors:=PrimeDivisors(N);
if not (Size(InvG2)=1 and Size(InvGAb)=2 and Size(Divisors)=1) then
  return fail;
fi;

p:=Divisors[1];
m:=Log(InvG2[1],p);
n2:=Log(InvGAb[1],p);
n1:=Log(InvGAb[2],p);

# We compute a basis of  G
BAb:=MinimalGeneratingSet(GAb);
if Order(BAb[1]) >= Order(BAb[2]) then
  bb1:=BAb[1];
  c:=BAb[2];
else
  bb1:=BAb[2];
  c:=BAb[1];
fi;
x:=0;
d:=One(GAb);
q:=p^n2;
c2:=c^q;
d2:=bb1^q;
while d<>c2 do
  x:=x+1;
  d:=d*d2;
od;
bb2:=c*bb1^(-x);
b1:=PreImagesRepresentative(e,bb1);
b2:=PreImagesRepresentative(e,bb2);
a:=Comm(b2,b1);


############################3
# #Experiment
# bb1:=b1;
# bb2:=b2;
# b1:=bb1^13;
# b2:=bb1^(p^(n1-n2))*bb2^-1 ;

########################


#To compute s(b)
s1:=1;
s2:=1;
if p=2 and m>=2 then
  a4:=a^(2^(m-2));
  if a4^b1*a4=One(G) then
    s1:=-1;
  fi;
  if a4^b2*a4=One(G) then
    s2:=-1;
  fi;
fi;
#We compute o(b)
o1:=0;
o2:=0;
b1p:=b1;
b2p:=b2;
while not (a^b1p   in [a,a^-1])   do
  b1p:=b1p^p;
  o1:=o1+1;
od;
while  not(a^b2p   in [a,a^-1]) do
  b2p:=b2p^p;
  o2:=o2+1;
od;

#Lemma 2.2
while not ( (s1=-1 or s2=1) and (n1>n2 or s1=s2) and (o1=0 or  (0<o1 and o1=o2 and s1=-1 and s2=-1) or (0=o2 and 0<o1 and n2<n1) or (0<o2 and o2<o1 and o1<o2+n1-n2))) do
  if s1=1 and s2=-1 then
    b1:=b1*b2;
    s1:=-1;
    o1:= Maximum(o1,o2); #Not completeley sure about this
    o1:=0;
    b1p:=b1;
    while not (a^b1p   in [a,a^-1])   do
      b1p:=b1p^p;
      o1:=o1+1;
    od;
  fi;
  if n1=n2 and s1<>s2 then
    b2:=b1*b2;
    s2:=-1;
    o2:=Maximum(o1,o2);
    o2:=0;
    b2p:=b2;
    while  not(a^b2p   in [a,a^-1]) do
      b2p:=b2p^p;
      o2:=o2+1;
    od;
  fi;
    if o2>= o1  and not (o1=o2 and s1=-1 and s2=-1) then
      c:=b2^(-p^(o2-o1));
      while a^b1<>a and  not (s1=-1 and a^b1=a^-1) do
        b1:=b1*c;
      od;
      o1:=0;
    fi;
    if o2<o1 then
      if n1=n2 and s1=s2 then
        bb1:=b1;
        b1:=b2;
        b2:=bb1;
        o:=o1;
        o1:=o2;
        o2:=o;
      fi;
      if o2>0 and o1>= o2+n1-n2 then
        c:=b1^(-p^(o1-o2));
        while a^b2<>a and   not (s2=-1 and a^b2=a^-1) do
          b2:=c*b2;
        od;
        o2:=0;
      fi;
    fi;
od;

###########################################3
#Now (o_1,o_2)=(o1,o2) is the optimum value, and   b\in B'.


a:=Comm(b2,b1);
bb1:=b1;
bb2:=b2;
#Calculamos r_i
r1:=s1*(1+ p^(m-o1)) mod p^m;
if Minimum(o1,o2)=0 then
  r2:=s2*(1+p^(m-o2)) mod p^m;
else
  r2:= s2*(1+p^(m-o1))^(p^(o1-o2)) mod p^m;
fi;

#We force b\in B_r
ar1:=a^r1;
ar2:=a^r2;
x:=1;
while a^b1<> ar1 or RemInt(x,p)=0 do  #No estoy seguro de si hace falta comprobar que x e y son coprimos con p, o se sigue de la igualdad.
  b1:=b1*bb1;
  x:=x+1;
od;
y:=1;
while a^b2<> ar2 or RemInt(y,p)=0 do
  b2:=b2*bb2;
  y:=y+1;
od;


#Now b\in B_r
#####################################
#We compute O(b)=o'(b).
O1:=Log(Order(b1),p)-n1;
O2:=Log(Order(b2),p)-n2;

#


#
#
#Lemma 4.2
if s1=1 then
#Case (i)
  if p>2 or not ( (0<m-n2 and m-n2=o1-o2) or m=n1) then
     if o1=0 then
       while not  (O1<=O2 and O2<=O1+o2+n1-n2) do
         if O2>O1+o2+n1-n2 then
           b1:=b1*b2^(p^o2);
           O1:=Log(Order(b1),p)-n1;
         fi;
         if O1>O2 then
           b2:=b1^(p^(n1-n2))*b2;
           O2:=Log(Order(b2),p)-n2;
         fi;
       od;
     fi;
     #
     if o2=0 and 0<o1 then
       while not (O2<=n1-n2+O1 and O1<= Maximum(0,o1-n1+n2)+O2 ) do
         if O2>n1-n2+O1 then
           b1:=b1*b2;
           O1:=n2+O2-n1;
              O1:=Log(Order(b1),p)-n1;
         fi;
         if O1> Maximum(0,o1-n1+n2)+O2 then
           b2:=b1^(p^Maximum(n1-n2,o1))*b2;
           O2:=Log(Order(b2),p)-n2;
         fi;
       od;
     fi;
     #
     if 0<o1*o2 then
       while not (O1<=O2 and O2<=O1+n1-n2) do
         if O2>O1+n1-n2 then
           b1:=b1^(1-p^(o1-o2))*b2;
           O1:=n2+O2-n1;
           O1:=Log(Order(b1),p)-n1;
         fi;
         if O1>O2 then
           b2:=b1^(p^(n1-n2))*b2^(1-p^(n1-n2-o1+o2)); ##############################################3
           O2:=O1;
           O2:=Log(Order(b2),p)-n2;
           ##################################################
           ########################################################
         fi;
       od;
     fi;
     #
  fi;
  #Case (ii)
  if p=2 and 0<m-n2 and m-n2=o1-o2 then
    if n1>m  and O2>O1+n1-n2 then
      b1:=b1^(1-p^(o1-o2))*b2;
      #O1:=n2+O2-n1;
      O1:=Log(Order(b1),2)-n1;
    fi;
    if n1<=m and not (1<=O1 and O2<=O1+n1-n2) then
        b1:=b1*b2;
        #O1:=n2+O2-n1;
        O1:=Log(Order(b1),2)-n1;
    fi;
  fi;
  #Case (iii)
  if p=2 and m=n1 and not (0<m-n2 and m-n2=o1-o2) then
    if n2>=m then
      while   not ( (O1<= O2 and O2<=O1+o2+n1-n2 and (O2>0 or n1>m)) or (m=n1 and O2=0 and O1=1)) do
          if o2=0 and O2>O1+o2 then
            bb1:=b1;
            b1:=b2;
            b2:=bb1;
            OO1:=O1;
            O1:=O2;
            O2:=OO1;
          fi;
          if o2>0 and O2>O1+o2 then
            b1:=b1*b2^(p^o2);
            #O1:=O2-o2;
            O1:=Log(Order(b1),2)-n1;
          fi;
          if not (( 1<=O2 and O1<=O2) or (O2=0 and O1=1)) then
            b2:=b1*b2;
            O2:=Log(Order(b2),2)-n2;
          fi;
      od;
    fi;
    if n2<m and not ( O1+Minimum(0,n1-n2-o1)<=O2 and O2<=O1+n1-n2 and O1>0 )  then
        b1:=b1*b2;
        #O1:=n2+O2-n1;
        O1:=Log(Order(b1),2)-n1;
    fi;
  fi;
fi;

#Lemma 4.3
if s1=-1 and s2=1 then
  if m<=n2 and not (O1<= O2 or (o2=0 and 0<n1-n2 and n1-n2<o1)) then
    b2:=b1^(2^(n1-n2))*b2;
    O2:=Log(Order(b2),2)-n2;
  fi;
  if m>n2 and not (O1=1 or o1+1<>n1) then
    b1:=b1^(1-p^(o1-o2))*b2;
    O1:=Log(Order(b1),2)-n1;
  fi;
fi;

#Lemma 4.4
if s1=-1 and s2=-1 then
  #Case (i)
  if o1+1=n1 and o2=0 and 0<o1 and n2=1 and Maximum(O1,O2)=0 then
    b2:=b1^(p^o1)*b2;
    O2:=Log(Order(b2),2)-n2;
  fi;
#Case (ii)
  if  o1+1<>n1 or o2<>0 or o1=0 or n2 <>1 then
      if n1>n2 and o1=0 and O1>O2 then
        b2:=b1^(2^(n1-n2))*b2;
        O2:=Log(Order(b2),2)-n2;
      fi;
      if n1>n2 and 0<o1 and o1=o2 and O1>O2 then
        b2:=b1^(2^(n1-n2))*b2^(1-2^(n1-n2));
        O2:=Log(Order(b2),2)-n2;
      fi;
      if n1=n2 and o1=o2  and O2>O1 then
        bb1:=b1;
        b1:=b2;
        b2:=bb1;
        OO1:=O1;
        O1:=O2;
        O2:=OO1;
      fi;
      if o2=0 and 0<o1 and O1+Minimum(0,n1-n2-o1)>O2 then
        b2:=b1^(2^Maximum(n1-n2,o1))*b2;
        O2:=Log(Order(b2),2)-n2;
      fi;
      if o1*o2>0 and o1<>o2 and O1>O2 then
        b1:=b1^(2^(n1-n2))*b2^(1-p^(n1-n2+o2-o1));
        O1:=Log(Order(b1),2)-n1;
      fi;

  fi;
fi;

################################
#Now we have that o'(b)=(o_1',o_2')=(O1,O2) is the optimum value.

#################################

#Compute u(b)
bb1:=b1;
bb2:=b2;
aa:=Comm(bb2,bb1);




b1pn1:=bb1^(p^n1);
b2pn2:=bb2^(p^n2);
apmO1:=aa^(p^(m-O1));
apmO2:=aa^(p^(m-O2));
x:=apmO1;
uu1:=1;
uu2:=1;
while x<> b1pn1 do
  uu1:=uu1+1;
  x:=x*apmO1;
od;
x:=apmO2;
while x<> b2pn2 do
  uu2:=uu2+1;
  x:=x*apmO2;
od;

#Now (uu1,uu2)=u(b).
#Lemma 5.1
if s1=1 and s2=1 then
  a1:=Minimum(O1, o2+Minimum(n1-n2+O1-O2,0));
  pa1:=p^a1;
  #########
  if o1=0 then
    a2:=0;
    if a1=0 then
      r:=1;
      q:=uu1-1;
    else
     q:=QuoInt(uu1, pa1);
     r:=uu1-q*pa1;
   fi;
   x2:=0;
   x1:=uu2;
    if a1=O1 then
       y1:=0;
       y2:=1;
    fi;
    if a1=o2 then
      rprime:=r^-1 mod p^m;
      y1:=0;
      y2:=rprime*uu1;
    fi;
    if a1=o2+n1-n2+O1-O2 and a1<o2 then
      y1:=-q*p^o2;
      y2:=1;
    fi;
   u1:=r;
   u2:=1;
  fi;
  ########
  if o2=0 and 0<o1 then
    a2:=Minimum (o1, O2, O2-O1+Maximum(0,o1+n2-n1));
    pa2:=p^a2;
    if a2=0 then
      r:=1;
      q:=uu2-1;
    else
      q:=QuoInt(uu2,pa2);
      r:=uu2-q*pa2;
    fi;
      y1:=0;
      y2:=uu1;
     if a2=O2 then
       x1:=1;
       x2:=0;
     fi;
     if a2=O2-O1+Maximum(0,o1+n2-n1) and a2<o1 then
       x1:=1;
       x2:=-q*p^Maximum(n1-n2,o1);
     fi;
     if a2=o1 then
       rprime:=r^-1 mod p^m;
       delta:= 0;
       if p=2 and m-n2=o1 then
         delta:=1;
       fi;
       x1:=rprime*uu2+delta*q*2^(m-1);
       x2:=0;
     fi;
    u1:=1;
    u2:=r;
   fi;
# ###########
  if 0<o2 and o2<o1 then
    a2:=Minimum(o1-o2,O2-O1);
    a1prime:=n1-n2-Maximum(o1-o2,O2-O1);
    if a2=0 then
      r:=1;
      q:=uu2-1;
    else
      q:=QuoInt(uu2,p^a2);
      r:=uu2-q*p^a2;
    fi;
    if uu1 mod p=q*p^(a1prime) mod p and 0<a1 then
      R2:=r+p^a2;
      q2:=q-1;
    else
      R2:=r;
      q2:=q;
    fi;
    R:=uu1-q2*p^a1prime;
    if a1=0 then
      R1:=1;
      q1:=R-1;
    else
      q1:=QuoInt(R,p^a1);
      R1:=R-q1*p^a1;
      if R1<0 then
        q1:=q1-1;
        R1:=R1+p^a1;
      fi;
    fi;
    if RemInt(R,p)<>0 then
    Rprime:=R^-1 mod p^m;
    fi;
    R1prime:=R1^-1 mod p^m;
    R2prime:=R2^-1 mod p^m;
    delta:=0;
    if p=2 and m-n2=o1-o2 then
      delta:=1;
    fi;
    ####################
    #The cases cases of Table 3 (page 17).
    if a2=O2-O1 and a1=o2 then
        x1:=1;
        y1:=0;
        x2:=-R1prime*q2*p^(n1-n2);
        y2:=R1prime*uu1;
    fi;
    if a2=O2-O1 and a1=O1 then
        x1:=1;
        y1:=0;
        x2:=-Rprime*q2*p^(n1-n2);
        y2:=Rprime*uu1;
    fi;
    if a2<>O2-O1 and a1=o2 then
        x1:=R2prime*uu2+ delta*q2*2^(O2-1);
        y1:=-R2prime*q2- delta*q2*2^(O2-1-o1+o2);
        x2:=0;
        y2:=R1prime*R;
    fi;
    if a2<>O2-O1 and a1=O1 then
        x1:=R2prime*uu2+ delta*q2*2^(O2-1);
        y1:=-R2prime*q2- delta*q2*2^(O2-1-o1+o2);
        x2:=0;
        y2:=1;
    fi;
    ###################
    u1:=R1;
    u2:=R2;
  fi;
fi;
######################################



#Lemma 5.2
if  s1=-1  then
  if s2=-1 or m<=n2 or (O1=0 and (o1=0 or o2+1<>n2)) or (O1=1 and o2=0 and n1-n2<o1)  or uu2<=2^(m-n2) then
    u1:=uu1;
    u2:=uu2;
    x1:=1;
    y1:=0;
    x2:=0;
    y2:=1;
  else
    u1:=uu1;
    u2:=RemInt(uu2, 2^(m-n2));
   if O1=1 then
    if o2=0 and 0<o1 and n1=o1+1 and n2=1 then
      x1:=1-2^o1;
      y1:=0;
      x2:=2^o1;
      y2:=1;
    else
      if o1=0 then
        x1:=1;
        y1:=0;
        x2:=2^(n1-n2);
        y2:=1;
      fi;
      if o2=0 and 0<o1 and o1<=n1-n2 then
        x1:=1;
        y1:=0;
        x2:=2^(n1-n2);
        y2:=1;
      fi;
      if o1*o2>0 then
          x1:=1;
          y1:=0;
          x2:=2^(n1-n2);
          y2:=1-2^(n1-n2-o1+o2);
      fi;
    fi;
   fi;
   if O1=0 and o2+1=n2 and o1>0  then
     # x1:=1-2^((o1-o2));
     # y1:=2^(o1-o2);
     x1:=1-2^(o1-o2);
     y1:=1;
     x2:=0;
     y2:=1;
   fi;
  fi;#else
fi;
b1:=bb1^x1*bb2^y1;
b2:=bb1^x2*bb2^y2;
# #b1, b2 is a optimal basis, and u1,u2 is the invariant.
# ################################
#O1:=-1; O2:=-1; u1:=-1;u2:=-1;
return [[p,m,n1,n2,s1,s2,o1,o2,O1,O2,u1,u2], [b1,b2]];
end;

Invariants:=function(G)
  local IB;
	IB:=InvariantsAndBasis(G);
  if IB=fail then
    return fail;
  else
    return IB[1];
  fi;
end;

AreIsomorphicGroups:=function(G,H)
  local IG,IH;
  IG:=Invariants(G);
  IH:=Invariants(H);
  if IG=fail or IH=fail then
    return fail;
  fi;
  if IG=IH then
    return true;
  else
    return false;
  fi;
end;



IsomorphismCbAGroups:=function(G,H)
    local IBG,IBH;
    IBG:=InvariantsAndBasis(G);
    IBH:=InvariantsAndBasis(H);
    if IBG=fail or IBH=fail or IBG[1]<>IBH[1] then
      return fail;
    else
      return GroupHomomorphismByImagesNC(G,H, IBG[2],IBH[2]);
    fi;
  end;











  ############################################
  ###Functions to check that our results are correct (for small orders, at least).
   LoadPackage("ANUPQ");

   # Next function computes all the cyclic-by-abelian groups of order p^n
  DescendantsCbA2Gen := function(p,n)
  local G, descen;
  LoadPackage("ANUPQ");
  G:=SmallGroup(p^2,2);
  descen :=  PqDescendants( G : ClassBound := n-1, OrderBound := n,   Metabelian := true);
  return Filtered(descen, x-> Order(x)=p^n and IsCyclic(DerivedSubgroup(x)) and not IsAbelian(x));
  end;
 #########################################################################
  # Next function uses DescendientesCbA2Gen and CbA2genOrder to check whether the number of non-abelian
  # cyclic-by-abelian 2-generated p-groups of order   p^n coincides with the
  # number of allowed invariants according to the main theorem of the paper
  CheckNumber:= function(p,n)
  local grupos, para;
  grupos := DescendantsCbA2Gen(p,n);
  para :=  CbA2GenByOrder(p,n);
  return Length(grupos)=Length(para);
  end;


  # Next function uses DescendientesCbA2Gen, CbA2genOrder and Invariants to check whether the lists of invariants of non-abelian
  # cyclic-by-abelian 2-generated p-groups of order  p^n coincides with the
  #  lists of allowed invariants according to the main theorem of the paper
  CheckIsoClasses:= function(p,n)
  local grupos, para;
  grupos := DescendantsCbA2Gen(p,n);
  para :=  CbA2GenByOrder(p,n);
  return SortedList(List(grupos,Invariants))=SortedList(para);;
  end;











  ####################################################3
  #This function if just to check if the invariants and basis obtained from InvariantsAneBasis are the correct ones.
  CheckBasis:=function(L)
    local G,IB,presentation,p,m,n1,n2,s1,s2,o1,o2,O1,O2,u1,u2,r1,r2,b,b1,b2,a,e;
    p:=L[1];
    m:=L[2];
    n1:=L[3];
    n2:=L[4];
    s1:=L[5];
    s2:=L[6];
    o1:=L[7];
    o2:=L[8];
    O1:=L[9];
    O2:=L[10];
    u1:=L[11];
    u2:=L[12];
    r1:=s1*(1+ p^(m-o1)) mod p^m;
   if Minimum(o1,o2)=0 then
    r2:=s2*(1+p^(m-o2)) mod p^m;
   else
    r2:= s2*(1+p^(m-o1))^(p^(o1-o2)) mod p^m;
   fi;
    G:=CbA2GenPcp(L);
    e:=One(G);
    IB:=InvariantsAndBasis(G);
    b:=IB[2];
    b1:=b[1];
    b2:=b[2];
    a:=Comm(b2,b1);
   presentation:= (a^(p^m)=e) and (a^b1=a^r1) and (a^b2=a^r2) and (b1^(p^n1)=a^(u1*p^(m-O1))) and (b2^(p^n2)=a^(u2*p^(m-O2)));
    #  presentation:= [(a^(p^m)=e) ,(a^b1=a^r1) ,(a^b2=a^r2) ,(b1^(p^n1)=a^(u1*p^(m-O1))), (b2^(p^n2)=a^(u2*p^(m-O2)))];
    return IB[1]=L and presentation;
  end;
