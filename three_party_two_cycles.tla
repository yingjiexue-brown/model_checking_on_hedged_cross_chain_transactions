----------------------- MODULE three_party_two_cycles -----------------------
EXTENDS Integers, TLC
(* --algorithm example
(*
The graph is A2B,B2A,B2C,C2A*)
variables
   \* a contract has three subcontracts: asset_contract and premium_escrow_contract and  premium_redeem_contract
    \* A swap contract has balance, timeout is initialized as -1 and it will be changed after it is escrowed;
    \* a deadline to be escrowed
    asset_contract = [A2B |->[balance |->100, timeout |-> -1, state |-> INIT,deadline |-> 6],
                     B2C |->[balance |->50, timeout |-> -1, state |-> INIT,deadline |-> 7],
                     B2A |->[balance |->50, timeout |-> -1, state |-> INIT,deadline |-> 7],
                     C2A |->[balance |->50, timeout |-> -1, state |-> INIT,deadline |-> 8]
                     ],
                     
    premium_escrow_contract = [A2B |->[balance |->10, timeout |-> -1, state |-> INIT,deadline |-> 0],
                                B2C |->[balance |->5, timeout |-> -1, state |-> INIT,deadline |-> 1],
                                B2A |->[balance |->5, timeout |-> -1, state |-> INIT,deadline |-> 1],
                                C2A |->[balance |->5, timeout |-> -1, state |-> INIT,deadline |-> 2]
                                ],
                     
    premium_redeem_contract_sa = [A_ON_CA|->[balance |->3, timeout |-> -1, state |-> INIT,deadline |-> 3],
                                  A_ON_BA |->[balance |->2, timeout |-> -1, state |-> INIT,deadline |-> 3],
                                  CA_ON_BC |->[balance |->2, timeout |-> -1, state |-> INIT,deadline |-> 4],
                                  BA_ON_AB |->[balance |->1, timeout |-> -1, state |-> INIT,deadline |-> 4],
                                  BCA_ON_AB |->[balance |->1, timeout |-> -1, state |-> INIT,deadline |-> 5]  
                                  ],
               
   
    path_signature_sa = [A_ON_CA|->[timeout |-> 9, state |-> INIT],
                        A_ON_BA|->[timeout |-> 9, state |-> INIT],
                        CA_ON_BC |->[timeout |-> 10, state |-> INIT],
                        BA_ON_AB |->[timeout |-> 10, state |-> INIT],
                        BCA_ON_AB |->[timeout |-> 11, state |-> INIT]
                        ],                                 
    
    wallet = [ALICE |-> [balance|-> 100+10+5,input|->115], BOB|-> [balance|-> 100+10+2,input|->112],CAROL |->[balance|->50+5+2,input|->57]],
    \* global clock
    clock = 0,
    \* indicating whether a step is considered in the model
    step_considered = [s \in STEPS |->FALSE],
    conforming = [p \in  PARTIES |->TRUE],
    step_taken = [s \in STEPS |->FALSE],
    ending = [p\in PROCESSES|->FALSE],
    party_contract_map = [ALICE|->"A2B",BOB|->"B2C",CAROL|->"C2A"]
define
 INIT == 0 ESCROW == 1 REDEEMED == 2 REFUNDED == 3  ACTIVATED == 4 REFUNDED2 == 5 LOST == 6 EXPIRED == 7 RELEASED == 8 \* contract states
 ALICE == 0 BOB == 1 CAROL == 2  \* ID for parties
 A2B == 0 B2C == 1 C2A == 2 B2A == 3 CLOCK == 4  \* process ids
 LIMIT == 12                        \* max clock value
 PARTIES == {"ALICE", "BOB", "CAROL"}            \* parties
 PROCESSES == {A2B,B2C,C2A,B2A}
 SP_P_AB == 0 SP_P_BA == 1 SP_P_BC ==2 SP_P_CA==3 
 SP_R_SA_A_ON_CA == 4 SP_R_SA_A_ON_BA ==5 SP_R_SA_CA_ON_BC ==6  SP_R_SA_BA_ON_AB ==7 SP_R_SA_BCA_ON_AB==8
 SAB ==9 SBA==10  SBC==11 SCA==12 
 SSA_A_ON_CA ==13 SSA_A_ON_BA ==14 SSA_CA_ON_BC ==15 SSA_BA_ON_AB== 16 SSA_BCA_ON_AB ==17
 
 STEPS == {SP_P_AB,SP_P_BA,SP_P_BC,SP_P_CA,SP_R_SA_A_ON_CA,SP_R_SA_A_ON_BA,SP_R_SA_CA_ON_BC,SP_R_SA_BA_ON_AB,SP_R_SA_BCA_ON_AB,
            SAB,SBA,SBC,SCA,SSA_A_ON_CA,SSA_A_ON_BA,SSA_CA_ON_BC,SSA_BA_ON_AB,SSA_BCA_ON_AB}
 SWPCN == {"A2B","B2C","B2A","C2A"}
 PATHSIGS == {"A_ON_CA","A_ON_BA","CA_ON_BC","BA_ON_AB","BCA_ON_AB"}
 ended == ending[0]/\ending[1]/\ending[2]/\ending[3]
 
 \* below are properties that we are interested to check
 conformingliveness == /\ \A x \in PARTIES: ended/\conforming[x]
 nounderwater == /\ \A x \in PARTIES: ended/\conforming[x]=>wallet[x].balance>=wallet[x].input
 compensated == /\ \A x\in PARTIES:  ended/\asset_contract[party_contract_map[x]].state=REFUNDED/\conforming[x]=>wallet[x].balance>=wallet[x].input+1
 compensated_BA == ended /\ conforming["BOB"]/\asset_contract["B2A"].state = REFUNDED =>wallet["BOB"].balance>=wallet["BOB"].input+1
 contractliveness == (ended /\ \A x\in PARTIES: conforming[x]) => (\A x \in SWPCN, y \in PATHSIGS: asset_contract[x].state=REDEEMED/\premium_redeem_contract_sa[y].state = REFUNDED/\premium_escrow_contract[x].state =REFUNDED2)
 walletliveness == (ended /\ \A x\in PARTIES: conforming[x]) => (\A x \in PARTIES:wallet[x].balance=wallet[x].input)
 constant == wallet["ALICE"].balance+wallet["BOB"].balance+wallet["CAROL"].balance
 constant_expect == wallet["ALICE"].input+wallet["BOB"].input+wallet["CAROL"].input
end define;

\* Note: for model checking, first check conformingliveness can be true by ~conforminglivess 
\* then check  nounderwater, compensated,contractliveness,walletliveness,constant = 115+212+107

\* A2B process =======================================================================================================
fair process a2b = A2B begin 

P_P_AB: \*clock =0, Alice publishes premium_escrow(A,B)
    
    if clock<= premium_escrow_contract["A2B"].deadline /\ premium_escrow_contract["A2B"].state=INIT then 
               premium_escrow_contract["A2B"].state:=ESCROW 
              ||premium_escrow_contract["A2B"].timeout:=premium_redeem_contract_sa["BCA_ON_AB"].deadline;\* since premium_redeem_contract_sa["BCA_ON_AB"].deadline=5
              step_taken[SP_P_AB]:= TRUE;
    else
       conforming["ALICE"]:=FALSE;
    end if;
    step_considered[SP_P_AB]:= TRUE;

    
  
P_R_SA_BA_ON_AB: \* clock =4, Bob publishes premium_redeem(sa,ba) on ab
 if  step_taken[SP_P_AB]/\step_taken[SP_R_SA_A_ON_BA]/\clock<= premium_redeem_contract_sa["BA_ON_AB"].deadline /\ premium_redeem_contract_sa["BA_ON_AB"].state=INIT then 
       premium_redeem_contract_sa["BA_ON_AB"].state:=ESCROW 
              ||premium_redeem_contract_sa["BA_ON_AB"].timeout:=path_signature_sa["BA_ON_AB"].timeout;\*the path sig should be published before 10
              step_taken[SP_R_SA_BA_ON_AB]:= TRUE;
              if premium_escrow_contract["A2B"].state=ESCROW then
              premium_escrow_contract["A2B"].state:=ACTIVATED
              ||premium_escrow_contract["A2B"].timeout := asset_contract["A2B"].deadline;\* deadline for B2A to publish
              end if;
  end if;
  step_considered[SP_R_SA_BA_ON_AB]:= TRUE;
  \* determine conformity
  if  ~step_considered[SP_R_SA_A_ON_BA]/\clock<=premium_redeem_contract_sa["A_ON_BA"].deadline then
     conforming["BOB"]:=FALSE;
  elsif step_taken[SP_R_SA_A_ON_BA]/\step_taken[SP_P_AB]/\~step_taken[SP_R_SA_BA_ON_AB] then
      conforming["BOB"]:=FALSE;
  end if;
    
 
    
P_R_SA_BCA_ON_AB: \* clock =5, bob publishes premium_redeem(sa,bca) on AB
 if  step_taken[SP_P_AB]/\step_taken[SP_R_SA_CA_ON_BC]/\clock<= premium_redeem_contract_sa["BCA_ON_AB"].deadline /\ premium_redeem_contract_sa["BCA_ON_AB"].state=INIT then 
       premium_redeem_contract_sa["BCA_ON_AB"].state:=ESCROW 
              ||premium_redeem_contract_sa["BCA_ON_AB"].timeout:=path_signature_sa["BCA_ON_AB"].timeout;\*path signature publishes before 11
              step_taken[SP_R_SA_BCA_ON_AB]:= TRUE;
              if premium_escrow_contract["A2B"].state=ESCROW then
              premium_escrow_contract["A2B"].state:=ACTIVATED
              ||premium_escrow_contract["A2B"].timeout := asset_contract["A2B"].deadline;\*A2B should publish before 6
              end if;
  elsif premium_escrow_contract["A2B"].state=ESCROW then
          premium_escrow_contract["A2B"].state:=REFUNDED;
  end if;
  step_considered[SP_R_SA_BCA_ON_AB]:= TRUE;
  \*determining conformity
  if ~step_considered[SP_R_SA_CA_ON_BC]/\clock<=premium_redeem_contract_sa["CA_ON_BC"].deadline then
      conforming["BOB"]:=FALSE;
  elsif step_taken[SP_R_SA_CA_ON_BC]/\step_taken[SP_P_AB]/\~step_taken[SP_R_SA_BCA_ON_AB] then
       conforming["BOB"]:=FALSE;
  end if;


AB: \*clock =6, Alice publishes (A,B)
    
    if premium_escrow_contract["A2B"].state=ACTIVATED/\clock<= asset_contract["A2B"].deadline /\  asset_contract["A2B"].state=INIT then 
       asset_contract["A2B"].state:=ESCROW 
              || asset_contract["A2B"].timeout:=path_signature_sa["BCA_ON_AB"].timeout;\*path sig should publish before 11
              step_taken[SAB]:= TRUE;
              premium_escrow_contract["A2B"].state:=REFUNDED2;
             
     elsif premium_escrow_contract["A2B"].state=ACTIVATED then
           premium_escrow_contract["A2B"].state:=LOST; 
           wallet["ALICE"].balance:= wallet["ALICE"].balance -  premium_escrow_contract["A2B"].balance
           ||wallet["BOB"].balance := wallet["BOB"].balance +  premium_escrow_contract["A2B"].balance        
    end if;
    step_considered[SAB]:= TRUE;
    \* determine conformity
    if premium_escrow_contract["A2B"].state>=ACTIVATED /\~step_taken[SAB] then 
       conforming["ALICE"]:=FALSE;
    end if;
      
   
SA_BA_ON_AB: \* clock =10, BOB publishes (sa,Ba) on AB
 if  step_taken[SAB]/\step_taken[SSA_A_ON_BA]/\clock<= path_signature_sa["BA_ON_AB"].timeout /\ path_signature_sa["BA_ON_AB"].state=INIT then 
       path_signature_sa["BA_ON_AB"].state:=RELEASED;
              step_taken[SSA_BA_ON_AB]:= TRUE;
             if asset_contract["A2B"].state = ESCROW then 
             asset_contract["A2B"].state := REDEEMED;
             wallet["BOB"].balance:= wallet["BOB"].balance + asset_contract["A2B"].balance
             ||wallet["ALICE"].balance := wallet["ALICE"].balance - asset_contract["A2B"].balance;
             end if;
             if premium_redeem_contract_sa["BA_ON_AB"].state = ESCROW then
             premium_redeem_contract_sa["BA_ON_AB"].state:= REFUNDED;
             end if;
    else
        if step_taken[SAB]/\premium_redeem_contract_sa["BA_ON_AB"].state = ESCROW then
           premium_redeem_contract_sa["BA_ON_AB"].state:= LOST;
           wallet["ALICE"].balance:= wallet["ALICE"].balance + premium_redeem_contract_sa["BA_ON_AB"].balance
          ||wallet["BOB"].balance := wallet["BOB"].balance - premium_redeem_contract_sa["BA_ON_AB"].balance
        end if;
    end if;
 step_considered[SSA_BA_ON_AB]:= TRUE;
 \* determine conformity
 if ~step_considered[SSA_A_ON_BA]/\clock<=path_signature_sa["A_ON_BA"].timeout then
    conforming["BOB"]:=FALSE;
 elsif step_taken[SAB]/\step_taken[SSA_A_ON_BA] /\ ~step_taken[SSA_BA_ON_AB] then
     conforming["BOB"]:=FALSE;
 end if;
 
SA_BCA_ON_AB: \* clock =9, bob publishes premium_redeem(sa,bca) on AB
 if step_taken[SAB]/\step_taken[SSA_CA_ON_BC]/\clock<= path_signature_sa["BCA_ON_AB"].timeout /\ path_signature_sa["BCA_ON_AB"].state=INIT then 
       path_signature_sa["BCA_ON_AB"].state:=RELEASED; 
              step_taken[SSA_BCA_ON_AB]:= TRUE;
             if asset_contract["A2B"].state = ESCROW then  
             asset_contract["A2B"].state := REDEEMED;
             wallet["ALICE"].balance:= wallet["ALICE"].balance - asset_contract["A2B"].balance
             ||wallet["BOB"].balance := wallet["BOB"].balance + asset_contract["A2B"].balance;
             end if;
             if premium_redeem_contract_sa["BCA_ON_AB"].state = ESCROW then
             premium_redeem_contract_sa["BCA_ON_AB"].state:= REFUNDED;
             end if;
    else
        if asset_contract["A2B"].state = ESCROW  then
           asset_contract["A2B"].state := REFUNDED;
        end if;
        if premium_redeem_contract_sa["BCA_ON_AB"].state = ESCROW then
           premium_redeem_contract_sa["BCA_ON_AB"].state:= LOST;
           wallet["ALICE"].balance:= wallet["ALICE"].balance +premium_redeem_contract_sa["BCA_ON_AB"].balance
          ||wallet["BOB"].balance := wallet["BOB"].balance - premium_redeem_contract_sa["BCA_ON_AB"].balance
        end if;
    end if;
 step_considered[SSA_BCA_ON_AB]:= TRUE;
 \* determine comformity
 if step_considered[SSA_CA_ON_BC]/\clock<= path_signature_sa["CA_ON_BC"].timeout then
    conforming["BOB"]:=FALSE;
 elsif step_taken[SAB]/\step_taken[SSA_CA_ON_BC] /\ ~step_taken[SSA_BCA_ON_AB] then
    conforming["BOB"]:=FALSE;
 end if;
 ending[A2B] :=TRUE;
end process 

\* B2C process =======================================================================================================
fair process b2c = B2C begin 

P_P_BC: \*clock =1, Bob publishes premium_escrow(B,C)
  if clock<= premium_escrow_contract["B2C"].deadline /\ premium_escrow_contract["B2C"].state=INIT then 
       premium_escrow_contract["B2C"].state:=ESCROW 
              ||premium_escrow_contract["B2C"].timeout:=premium_redeem_contract_sa["CA_ON_BC"].deadline;\* premium_redeem_contract_sa["CA_ON_BC"].deadline =4
              step_taken[SP_P_BC]:= TRUE;
    else
       skip;
    end if;
   step_considered[SP_P_BC]:= TRUE;
   
   \*determine conformity
   if ~step_considered[SP_P_AB] /\ clock<=premium_escrow_contract["A2B"].deadline then
       conforming["BOB"]:=FALSE;
   elsif ~step_taken[SP_P_AB]/\step_taken[SP_P_BC] then
     conforming["BOB"]:=FALSE;
   elsif step_taken[SP_P_AB]/\~step_taken[SP_P_BC] then
     conforming["BOB"]:=FALSE;
   end if;
 
P_R_SA_CA_ON_BC: \* clock =4, carol publishes premium_redeem(sa,ca) on bc
 if  step_taken[SP_P_BC]/\step_taken[SP_R_SA_A_ON_CA]/\clock<= premium_redeem_contract_sa["CA_ON_BC"].deadline /\ premium_redeem_contract_sa["CA_ON_BC"].state=INIT then 
       premium_redeem_contract_sa["CA_ON_BC"].state:=ESCROW 
              ||premium_redeem_contract_sa["CA_ON_BC"].timeout:=path_signature_sa["CA_ON_BC"].timeout;\*the path sig should be published before 10
              step_taken[SP_R_SA_CA_ON_BC]:= TRUE;
              if premium_escrow_contract["B2C"].state=ESCROW then
              premium_escrow_contract["B2C"].state:=ACTIVATED
              ||premium_escrow_contract["B2C"].timeout := asset_contract["B2C"].deadline;\* deadline for B2C to publish
              end if;
  elsif premium_escrow_contract["B2C"].state=ESCROW then
        premium_escrow_contract["B2C"].state:=REFUNDED;
  end if;
  step_considered[SP_R_SA_CA_ON_BC]:= TRUE;
  
  \* determine conformity
  if ~step_considered[SP_R_SA_A_ON_CA]/\clock<=premium_redeem_contract_sa["A_ON_CA"].deadline then 
     conforming["CAROL"]:=FALSE;
  elsif step_taken[SP_R_SA_A_ON_CA]/\step_taken[SP_P_BC]/\~step_taken[SP_R_SA_CA_ON_BC] then
      conforming["CAROL"]:=FALSE;
  end if;
    
 BC: \*clock =7, Bob publishes (B,C)
  if premium_escrow_contract["B2C"].state=ACTIVATED/\clock<= asset_contract["B2C"].deadline /\ asset_contract["B2C"].state=INIT then 
       asset_contract["B2C"].state:=ESCROW 
              ||asset_contract["B2C"].timeout:=path_signature_sa["CA_ON_BC"].timeout;\* should be redeemed before 10
              step_taken[SBC]:= TRUE;
          premium_escrow_contract["B2C"].state:=REFUNDED2;
  elsif premium_escrow_contract["B2C"].state=ACTIVATED then
           premium_escrow_contract["B2C"].state:=LOST; 
           wallet["CAROL"].balance := wallet["CAROL"].balance + premium_escrow_contract["B2C"].balance
          ||wallet["BOB"].balance := wallet["BOB"].balance - premium_escrow_contract["B2C"].balance
           
   
   end if;
  step_considered[SBC]:= TRUE;
  \*determine conformity
   if  ~step_considered[SAB]/\clock<=asset_contract["A2B"].deadline then
        conforming["BOB"]:=FALSE;
   elsif step_taken[SAB]/\premium_escrow_contract["B2C"].state>=ACTIVATED /\~step_taken[SBC] then 
       conforming["BOB"]:=FALSE;
   elsif ~step_taken[SAB]\/step_taken[SBC] then
       conforming["BOB"]:=FALSE;
   end if;
  
SA_CA_ON_BC: \* clock =10, carol publishes (sa,ca) on bc
 if step_taken[SBC]/\ step_taken[SSA_A_ON_CA]/\clock<= path_signature_sa["CA_ON_BC"].timeout /\ path_signature_sa["CA_ON_BC"].state=INIT then 
       path_signature_sa["CA_ON_BC"].state:=RELEASED;
              step_taken[SSA_CA_ON_BC]:= TRUE;
             if asset_contract["B2C"].state = ESCROW then 
             asset_contract["B2C"].state := REDEEMED;
             wallet["CAROL"].balance:= wallet["CAROL"].balance + asset_contract["B2C"].balance
             ||wallet["BOB"].balance := wallet["BOB"].balance - asset_contract["B2C"].balance;
             end if;
             if premium_redeem_contract_sa["CA_ON_BC"].state = ESCROW then
             premium_redeem_contract_sa["CA_ON_BC"].state:= REFUNDED;
             end if;
    else
        if asset_contract["B2C"].state = ESCROW  then
           asset_contract["B2C"].state := REFUNDED;
        end if;
        if step_taken[SBC]/\premium_redeem_contract_sa["CA_ON_BC"].state = ESCROW then
           premium_redeem_contract_sa["CA_ON_BC"].state:= LOST;
           wallet["CAROL"].balance:= wallet["CAROL"].balance - premium_redeem_contract_sa["CA_ON_BC"].balance
          ||wallet["BOB"].balance := wallet["BOB"].balance + premium_redeem_contract_sa["CA_ON_BC"].balance
        end if;
    end if;
 step_considered[SSA_CA_ON_BC]:= TRUE;
 \* determine conformity
if ~step_considered[SSA_A_ON_CA]/\clock<=path_signature_sa["A_ON_CA"].timeout then
    conforming["CAROL"]:=FALSE;
elsif step_taken[SBC]/\step_taken[SSA_A_ON_CA] /\ ~step_taken[SSA_CA_ON_BC] then
     conforming["CAROL"]:=FALSE;
 end if;
 ending[B2C] :=TRUE;
end process
    
\* C2A process =======================================================================================================
    
fair process c2a = C2A begin

P_P_CA: \*clock =0, Carol publishes premium_escrow(C,A) 
    if clock<= premium_escrow_contract["C2A"].deadline /\ premium_escrow_contract["C2A"].state=INIT then 
       premium_escrow_contract["C2A"].state:=ESCROW 
              ||premium_escrow_contract["C2A"].timeout:=premium_redeem_contract_sa["A_ON_CA"].deadline;\*since premium_redeem_contract_sa["A_ON_CA"].deadline=3
              step_taken[SP_P_CA]:= TRUE;
    else
       skip;
    end if;
    step_considered[SP_P_CA]:= TRUE;
   \* determine conformity 
   if ~step_considered[SP_P_BC]/\ clock<=premium_escrow_contract["B2C"].deadline then 
      conforming["CAROL"]:=FALSE;
   elsif step_taken[SP_P_BC]/\~step_taken[SP_P_CA] then
       conforming["CAROL"]:=FALSE;
   elsif ~step_taken[SP_P_BC]/\step_taken[SP_P_CA] then
       conforming["CAROL"]:=FALSE;
    end if;
    
P_R_SA_A_ON_CA: \* clock =3, Alice publishes premium_redeem(sa,a) on CA
 if  step_taken[SP_P_CA]/\clock<= premium_redeem_contract_sa["A_ON_CA"].deadline /\ premium_redeem_contract_sa["A_ON_CA"].state=INIT then 
       premium_redeem_contract_sa["A_ON_CA"].state:=ESCROW 
              ||premium_redeem_contract_sa["A_ON_CA"].timeout:=path_signature_sa["A_ON_CA"].timeout;\* since the path signature timeout is 9
              step_taken[SP_R_SA_A_ON_CA]:= TRUE;
              
              if premium_escrow_contract["C2A"].state=ESCROW then
              premium_escrow_contract["C2A"].state:=ACTIVATED
              ||premium_escrow_contract["C2A"].timeout := asset_contract["C2A"].deadline;\* deadline for C2A to publish
              end if;
  elsif premium_escrow_contract["C2A"].state=ESCROW then
        premium_escrow_contract["C2A"].state:=REFUNDED;
  else
       skip;
  end if;
  step_considered[SP_R_SA_A_ON_CA]:= TRUE;
  if  ~(step_considered[SP_P_CA]/\step_considered[SP_P_BA])\/clock<=premium_escrow_contract["C2A"].deadline then
      conforming["ALICE"]:=FALSE;
  elsif ~step_taken[SP_P_BA]/\ step_taken[SP_R_SA_A_ON_CA] then
     conforming["ALICE"]:=FALSE;
  elsif ~step_taken[SP_P_CA]/\ step_taken[SP_R_SA_A_ON_CA] then \*since SP_P_CA is on the same chain, we ignore step_considered[] condition
       conforming["ALICE"]:=FALSE;
  elsif step_taken[SP_P_BA]/\step_taken[SP_P_CA]/\~step_taken[SP_R_SA_A_ON_CA] then
       conforming["ALICE"]:=FALSE
  end if;
    

CA: \*clock =8, Carol publishes (C,A)
    if premium_escrow_contract["C2A"].state=ACTIVATED/\clock<= asset_contract["C2A"].deadline /\ asset_contract["C2A"].state=INIT then 
       asset_contract["C2A"].state:=ESCROW 
              ||asset_contract["C2A"].timeout:=path_signature_sa["A_ON_CA"].timeout;\*should be redeemed before 9
              step_taken[SCA]:= TRUE;
              premium_escrow_contract["C2A"].state:=REFUNDED2;
           
     elsif premium_escrow_contract["C2A"].state=ACTIVATED then
           premium_escrow_contract["C2A"].state:=LOST;
           wallet["ALICE"].balance := wallet["ALICE"].balance + premium_escrow_contract["C2A"].balance
           ||wallet["CAROL"].balance := wallet["CAROL"].balance - premium_escrow_contract["C2A"].balance  
    end if;
   step_considered[SCA]:= TRUE;
   \* determine conformity
    if ~step_considered[SBC]/\clock<=asset_contract["B2C"].deadline then
     conforming["CAROL"]:=FALSE;
    elsif ~step_taken[SBC]/\step_taken[SCA] then 
        conforming["CAROL"]:=FALSE;
    elsif step_taken[SBC]/\premium_escrow_contract["C2A"].state>=ACTIVATED /\~step_taken[SCA] then 
       conforming["CAROL"]:=FALSE;
    end if;
   
SA_A_ON_CA: \* clock =9, Alice publishes (sa,a) on CA
 if step_taken[SCA]/\clock<= path_signature_sa["A_ON_CA"].timeout /\ path_signature_sa["A_ON_CA"].state=INIT then 
       path_signature_sa["A_ON_CA"].state:=RELEASED;
              step_taken[SSA_A_ON_CA]:= TRUE;
             if asset_contract["C2A"].state = ESCROW then  
             asset_contract["C2A"].state := REDEEMED;
             wallet["CAROL"].balance:= wallet["CAROL"].balance - asset_contract["C2A"].balance
             ||wallet["ALICE"].balance := wallet["ALICE"].balance + asset_contract["C2A"].balance;
             end if;
             if premium_redeem_contract_sa["A_ON_CA"].state = ESCROW then
             premium_redeem_contract_sa["A_ON_CA"].state:= REFUNDED;
             end if;
    else
        if asset_contract["C2A"].state = ESCROW  then
           asset_contract["C2A"].state := REFUNDED;
        end if;
        if step_taken[SCA]/\premium_redeem_contract_sa["A_ON_CA"].state = ESCROW then
           premium_redeem_contract_sa["A_ON_CA"].state:= LOST;
           wallet["ALICE"].balance:= wallet["ALICE"].balance - premium_redeem_contract_sa["A_ON_CA"].balance
          ||wallet["CAROL"].balance := wallet["CAROL"].balance + premium_redeem_contract_sa["A_ON_CA"].balance
        end if;
    end if;
 step_considered[SSA_A_ON_CA]:= TRUE;
 if ~(step_considered[SCA]\/step_considered[SBA])/\clock<=asset_contract["C2A"].deadline then
     conforming["ALICE"]:=FALSE;
 elsif  ~(step_taken[SCA]/\step_taken[SBA])/\ step_taken[SSA_A_ON_CA] then
     conforming["ALICE"]:=FALSE;
 elsif step_taken[SCA]/\step_taken[SBA]/\ step_taken[SAB]/\~step_taken[SSA_A_ON_CA] then
     conforming["ALICE"]:=FALSE;
 end if;
 ending[C2A]:=TRUE;
end process   

\* b2a process ==============================================================

fair process b2a = B2A begin

P_P_BA: \*clock =1, Bob publishes premium_escrow(B,A)
    if  clock<= premium_escrow_contract["B2A"].deadline /\ premium_escrow_contract["B2A"].state=INIT then 
               premium_escrow_contract["B2A"].state:=ESCROW 
              ||premium_escrow_contract["B2A"].timeout:= premium_redeem_contract_sa["A_ON_BA"].deadline;\* since premium_redeem_contract_sa["A_ON_AB"].deadline=3
              step_taken[SP_P_BA]:= TRUE;
    end if;
    
    step_considered[SP_P_BA]:= TRUE;
    if ~step_considered[SP_P_AB]/\clock<=premium_escrow_contract["A2B"].deadline then
       conforming["BOB"]:=FALSE;
    elsif step_taken[SP_P_AB]/\~step_taken[SP_P_BA] then
       conforming["BOB"]:=FALSE;
    elsif ~step_taken[SP_P_AB]/\step_taken[SP_P_BA] then
       conforming["BOB"]:=FALSE;
    end if;
    
P_R_SA_A_ON_BA: \* clock =3, Alice publishes premium_redeem(sa,a) on BA
 if  step_taken[SP_P_BA]/\clock<= premium_redeem_contract_sa["A_ON_BA"].deadline /\ premium_redeem_contract_sa["A_ON_BA"].state=INIT then 
       premium_redeem_contract_sa["A_ON_BA"].state:=ESCROW 
              ||premium_redeem_contract_sa["A_ON_BA"].timeout:=path_signature_sa["A_ON_BA"].timeout;\* since the path signature timeout is 9
              step_taken[SP_R_SA_A_ON_BA]:= TRUE;
              
              if premium_escrow_contract["B2A"].state=ESCROW then
              premium_escrow_contract["B2A"].state:=ACTIVATED
              ||premium_escrow_contract["B2A"].timeout := asset_contract["B2A"].deadline;\* deadline for C2A to publish
              end if;
  elsif premium_escrow_contract["B2A"].state=ESCROW then
        premium_escrow_contract["B2A"].state:=REFUNDED;
  end if;
  step_considered[SP_R_SA_A_ON_BA]:= TRUE;
  if  ~(step_considered[SP_P_CA]/\step_considered[SP_P_BA])/\clock<=premium_escrow_contract["C2A"].deadline then
      conforming["ALICE"]:=FALSE;
  elsif ~step_taken[SP_P_BA]/\ step_taken[SP_R_SA_A_ON_BA] then \*since SP_P_CA is on the same chain, we ignore step_considered[] condition
       conforming["ALICE"]:=FALSE;
  elsif ~step_taken[SP_P_CA]/\step_taken[SP_R_SA_A_ON_BA] then
       conforming["ALICE"]:=FALSE;
  elsif step_taken[SP_P_BA]/\step_taken[SP_P_CA]/\~step_taken[SP_R_SA_A_ON_BA] then
       conforming["ALICE"]:=FALSE;
  end if;

 BA: \*clock =7, Bob publishes (B,A)
 
  if premium_escrow_contract["B2A"].state=ACTIVATED/\clock<= asset_contract["B2A"].deadline /\ asset_contract["B2A"].state=INIT then 
       asset_contract["B2A"].state:=ESCROW 
              ||asset_contract["B2A"].timeout:=path_signature_sa["A_ON_BA"].timeout;\* should be redeemed before 10
              step_taken[SBA]:= TRUE;
          premium_escrow_contract["B2A"].state:=REFUNDED2;

     elsif premium_escrow_contract["B2A"].state=ACTIVATED then
           premium_escrow_contract["B2A"].state:=LOST; 
           wallet["ALICE"].balance := wallet["ALICE"].balance + premium_escrow_contract["B2C"].balance
          ||wallet["BOB"].balance := wallet["BOB"].balance - premium_escrow_contract["B2A"].balance;
    end if;
  step_considered[SBA]:= TRUE;
  \*determine conformity
  
   if ~step_considered[SAB]/\clock<=asset_contract["A2B"].deadline then
       conforming["BOB"]:=FALSE;
   elsif step_taken[SAB]/\premium_escrow_contract["B2A"].state>=ACTIVATED /\~step_taken[SBA] then 
       conforming["BOB"]:=FALSE;
   elsif ~step_taken[SAB]/\step_taken[SBA] then 
       conforming["BOB"]:=FALSE;
   end if;
    
 SA_A_ON_BA: \* clock =9, Alice publishes (sa,a) on BA
 if step_taken[SBA]/\clock<= path_signature_sa["A_ON_BA"].timeout /\ path_signature_sa["A_ON_BA"].state=INIT then 
       path_signature_sa["A_ON_BA"].state:=RELEASED;
              step_taken[SSA_A_ON_BA]:= TRUE;
             if asset_contract["B2A"].state = ESCROW then  
             asset_contract["B2A"].state := REDEEMED;
             wallet["BOB"].balance:= wallet["BOB"].balance - asset_contract["B2A"].balance
             ||wallet["ALICE"].balance := wallet["ALICE"].balance + asset_contract["B2A"].balance;
             end if;
             if premium_redeem_contract_sa["A_ON_BA"].state = ESCROW then
             premium_redeem_contract_sa["A_ON_BA"].state:= REFUNDED;
             end if;
    else
        if asset_contract["B2A"].state = ESCROW  then
           asset_contract["B2A"].state := REFUNDED;
        end if;
        if step_taken[SBA]/\premium_redeem_contract_sa["A_ON_BA"].state = ESCROW then
           premium_redeem_contract_sa["A_ON_BA"].state:= LOST;
           wallet["ALICE"].balance:= wallet["ALICE"].balance - premium_redeem_contract_sa["A_ON_BA"].balance
          ||wallet["BOB"].balance := wallet["BOB"].balance + premium_redeem_contract_sa["A_ON_BA"].balance
        end if;
  end if;
 step_considered[SSA_A_ON_BA]:= TRUE;
 if ~(step_considered[SCA]/\step_considered[SBA])/\clock<=asset_contract["C2A"].deadline then
    conforming["ALICE"]:=FALSE;
 elsif step_taken[SCA]/\step_taken[SBA]/\ ~step_taken[SSA_A_ON_BA] then
     conforming["ALICE"]:=FALSE;
 elsif ~(step_taken[SCA]/\step_taken[SBA])/\ step_taken[SSA_A_ON_BA] then
     conforming["ALICE"]:=FALSE;
 end if;
 ending[B2A]:=TRUE;
 
end process

\* clock tick process =======================================================================================================
fair process Clock = CLOCK begin tick:
    while (clock <LIMIT) do
    tok: clock := clock + 1;
    end while;
 end process


end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-2a663c36010534d2242343cb32fd60f3
VARIABLES asset_contract, premium_escrow_contract, premium_redeem_contract_sa, 
          path_signature_sa, wallet, clock, step_considered, conforming, 
          step_taken, ending, party_contract_map, pc

(* define statement *)
INIT == 0 ESCROW == 1 REDEEMED == 2 REFUNDED == 3  ACTIVATED == 4 REFUNDED2 == 5 LOST == 6 EXPIRED == 7 RELEASED == 8
ALICE == 0 BOB == 1 CAROL == 2
A2B == 0 B2C == 1 C2A == 2 B2A == 3 CLOCK == 4
LIMIT == 12
PARTIES == {"ALICE", "BOB", "CAROL"}
PROCESSES == {A2B,B2C,C2A,B2A}
SP_P_AB == 0 SP_P_BA == 1 SP_P_BC ==2 SP_P_CA==3
SP_R_SA_A_ON_CA == 4 SP_R_SA_A_ON_BA ==5 SP_R_SA_CA_ON_BC ==6  SP_R_SA_BA_ON_AB ==7 SP_R_SA_BCA_ON_AB==8
SAB ==9 SBA==10  SBC==11 SCA==12
SSA_A_ON_CA ==13 SSA_A_ON_BA ==14 SSA_CA_ON_BC ==15 SSA_BA_ON_AB== 16 SSA_BCA_ON_AB ==17

STEPS == {SP_P_AB,SP_P_BA,SP_P_BC,SP_P_CA,SP_R_SA_A_ON_CA,SP_R_SA_A_ON_BA,SP_R_SA_CA_ON_BC,SP_R_SA_BA_ON_AB,SP_R_SA_BCA_ON_AB,
           SAB,SBA,SBC,SCA,SSA_A_ON_CA,SSA_A_ON_BA,SSA_CA_ON_BC,SSA_BA_ON_AB,SSA_BCA_ON_AB}
SWPCN == {"A2B","B2C","B2A","C2A"}
PATHSIGS == {"A_ON_CA","A_ON_BA","CA_ON_BC","BA_ON_AB","BCA_ON_AB"}
ended == ending[0]/\ending[1]/\ending[2]/\ending[3]


conformingliveness == /\ \A x \in PARTIES: ended/\conforming[x]
nounderwater == /\ \A x \in PARTIES: ended/\conforming[x]=>wallet[x].balance>=wallet[x].input
compensated == /\ \A x\in PARTIES:  ended/\asset_contract[party_contract_map[x]].state=REFUNDED/\conforming[x]=>wallet[x].balance>=wallet[x].input+1
compensated_BA == ended /\ conforming["BOB"]/\asset_contract["B2A"].state = REFUNDED =>wallet["BOB"].balance>=wallet["BOB"].input+1
contractliveness == (ended /\ \A x\in PARTIES: conforming[x]) => (\A x \in SWPCN, y \in PATHSIGS: asset_contract[x].state=REDEEMED/\premium_redeem_contract_sa[y].state = REFUNDED/\premium_escrow_contract[x].state =REFUNDED2)
walletliveness == (ended /\ \A x\in PARTIES: conforming[x]) => (\A x \in PARTIES:wallet[x].balance=wallet[x].input)
constant == wallet["ALICE"].balance+wallet["BOB"].balance+wallet["CAROL"].balance
constant_expect == wallet["ALICE"].input+wallet["BOB"].input+wallet["CAROL"].input


vars == << asset_contract, premium_escrow_contract, 
           premium_redeem_contract_sa, path_signature_sa, wallet, clock, 
           step_considered, conforming, step_taken, ending, 
           party_contract_map, pc >>

ProcSet == {A2B} \cup {B2C} \cup {C2A} \cup {B2A} \cup {CLOCK}

Init == (* Global variables *)
        /\ asset_contract = [A2B |->[balance |->100, timeout |-> -1, state |-> INIT,deadline |-> 6],
                            B2C |->[balance |->50, timeout |-> -1, state |-> INIT,deadline |-> 7],
                            B2A |->[balance |->50, timeout |-> -1, state |-> INIT,deadline |-> 7],
                            C2A |->[balance |->50, timeout |-> -1, state |-> INIT,deadline |-> 8]
                            ]
        /\ premium_escrow_contract = [A2B |->[balance |->10, timeout |-> -1, state |-> INIT,deadline |-> 0],
                                       B2C |->[balance |->5, timeout |-> -1, state |-> INIT,deadline |-> 1],
                                       B2A |->[balance |->5, timeout |-> -1, state |-> INIT,deadline |-> 1],
                                       C2A |->[balance |->5, timeout |-> -1, state |-> INIT,deadline |-> 2]
                                       ]
        /\ premium_redeem_contract_sa = [A_ON_CA|->[balance |->3, timeout |-> -1, state |-> INIT,deadline |-> 3],
                                         A_ON_BA |->[balance |->2, timeout |-> -1, state |-> INIT,deadline |-> 3],
                                         CA_ON_BC |->[balance |->2, timeout |-> -1, state |-> INIT,deadline |-> 4],
                                         BA_ON_AB |->[balance |->1, timeout |-> -1, state |-> INIT,deadline |-> 4],
                                         BCA_ON_AB |->[balance |->1, timeout |-> -1, state |-> INIT,deadline |-> 5]
                                         ]
        /\ path_signature_sa = [A_ON_CA|->[timeout |-> 9, state |-> INIT],
                               A_ON_BA|->[timeout |-> 9, state |-> INIT],
                               CA_ON_BC |->[timeout |-> 10, state |-> INIT],
                               BA_ON_AB |->[timeout |-> 10, state |-> INIT],
                               BCA_ON_AB |->[timeout |-> 11, state |-> INIT]
                               ]
        /\ wallet = [ALICE |-> [balance|-> 100+10+5,input|->115], BOB|-> [balance|-> 100+10+2,input|->112],CAROL |->[balance|->50+5+2,input|->57]]
        /\ clock = 0
        /\ step_considered = [s \in STEPS |->FALSE]
        /\ conforming = [p \in  PARTIES |->TRUE]
        /\ step_taken = [s \in STEPS |->FALSE]
        /\ ending = [p\in PROCESSES|->FALSE]
        /\ party_contract_map = [ALICE|->"A2B",BOB|->"B2C",CAROL|->"C2A"]
        /\ pc = [self \in ProcSet |-> CASE self = A2B -> "P_P_AB"
                                        [] self = B2C -> "P_P_BC"
                                        [] self = C2A -> "P_P_CA"
                                        [] self = B2A -> "P_P_BA"
                                        [] self = CLOCK -> "tick"]

P_P_AB == /\ pc[A2B] = "P_P_AB"
          /\ IF clock<= premium_escrow_contract["A2B"].deadline /\ premium_escrow_contract["A2B"].state=INIT
                THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["A2B"].state = ESCROW,
                                                                                   !["A2B"].timeout = premium_redeem_contract_sa["BCA_ON_AB"].deadline]
                     /\ step_taken' = [step_taken EXCEPT ![SP_P_AB] = TRUE]
                     /\ UNCHANGED conforming
                ELSE /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                     /\ UNCHANGED << premium_escrow_contract, step_taken >>
          /\ step_considered' = [step_considered EXCEPT ![SP_P_AB] = TRUE]
          /\ pc' = [pc EXCEPT ![A2B] = "P_R_SA_BA_ON_AB"]
          /\ UNCHANGED << asset_contract, premium_redeem_contract_sa, 
                          path_signature_sa, wallet, clock, ending, 
                          party_contract_map >>

P_R_SA_BA_ON_AB == /\ pc[A2B] = "P_R_SA_BA_ON_AB"
                   /\ IF step_taken[SP_P_AB]/\step_taken[SP_R_SA_A_ON_BA]/\clock<= premium_redeem_contract_sa["BA_ON_AB"].deadline /\ premium_redeem_contract_sa["BA_ON_AB"].state=INIT
                         THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["BA_ON_AB"].state = ESCROW,
                                                                                                  !["BA_ON_AB"].timeout = path_signature_sa["BA_ON_AB"].timeout]
                              /\ step_taken' = [step_taken EXCEPT ![SP_R_SA_BA_ON_AB] = TRUE]
                              /\ IF premium_escrow_contract["A2B"].state=ESCROW
                                    THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["A2B"].state = ACTIVATED,
                                                                                                       !["A2B"].timeout = asset_contract["A2B"].deadline]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED premium_escrow_contract
                         ELSE /\ TRUE
                              /\ UNCHANGED << premium_escrow_contract, 
                                              premium_redeem_contract_sa, 
                                              step_taken >>
                   /\ step_considered' = [step_considered EXCEPT ![SP_R_SA_BA_ON_AB] = TRUE]
                   /\ IF ~step_considered'[SP_R_SA_A_ON_BA]/\clock<=premium_redeem_contract_sa'["A_ON_BA"].deadline
                         THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                         ELSE /\ IF step_taken'[SP_R_SA_A_ON_BA]/\step_taken'[SP_P_AB]/\~step_taken'[SP_R_SA_BA_ON_AB]
                                    THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED conforming
                   /\ pc' = [pc EXCEPT ![A2B] = "P_R_SA_BCA_ON_AB"]
                   /\ UNCHANGED << asset_contract, path_signature_sa, wallet, 
                                   clock, ending, party_contract_map >>

P_R_SA_BCA_ON_AB == /\ pc[A2B] = "P_R_SA_BCA_ON_AB"
                    /\ IF step_taken[SP_P_AB]/\step_taken[SP_R_SA_CA_ON_BC]/\clock<= premium_redeem_contract_sa["BCA_ON_AB"].deadline /\ premium_redeem_contract_sa["BCA_ON_AB"].state=INIT
                          THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["BCA_ON_AB"].state = ESCROW,
                                                                                                   !["BCA_ON_AB"].timeout = path_signature_sa["BCA_ON_AB"].timeout]
                               /\ step_taken' = [step_taken EXCEPT ![SP_R_SA_BCA_ON_AB] = TRUE]
                               /\ IF premium_escrow_contract["A2B"].state=ESCROW
                                     THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["A2B"].state = ACTIVATED,
                                                                                                        !["A2B"].timeout = asset_contract["A2B"].deadline]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED premium_escrow_contract
                          ELSE /\ IF premium_escrow_contract["A2B"].state=ESCROW
                                     THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["A2B"].state = REFUNDED]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED premium_escrow_contract
                               /\ UNCHANGED << premium_redeem_contract_sa, 
                                               step_taken >>
                    /\ step_considered' = [step_considered EXCEPT ![SP_R_SA_BCA_ON_AB] = TRUE]
                    /\ IF ~step_considered'[SP_R_SA_CA_ON_BC]/\clock<=premium_redeem_contract_sa'["CA_ON_BC"].deadline
                          THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                          ELSE /\ IF step_taken'[SP_R_SA_CA_ON_BC]/\step_taken'[SP_P_AB]/\~step_taken'[SP_R_SA_BCA_ON_AB]
                                     THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED conforming
                    /\ pc' = [pc EXCEPT ![A2B] = "AB"]
                    /\ UNCHANGED << asset_contract, path_signature_sa, wallet, 
                                    clock, ending, party_contract_map >>

AB == /\ pc[A2B] = "AB"
      /\ IF premium_escrow_contract["A2B"].state=ACTIVATED/\clock<= asset_contract["A2B"].deadline /\  asset_contract["A2B"].state=INIT
            THEN /\ asset_contract' = [asset_contract EXCEPT !["A2B"].state = ESCROW,
                                                             !["A2B"].timeout = path_signature_sa["BCA_ON_AB"].timeout]
                 /\ step_taken' = [step_taken EXCEPT ![SAB] = TRUE]
                 /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["A2B"].state = REFUNDED2]
                 /\ UNCHANGED wallet
            ELSE /\ IF premium_escrow_contract["A2B"].state=ACTIVATED
                       THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["A2B"].state = LOST]
                            /\ wallet' = [wallet EXCEPT !["ALICE"].balance = wallet["ALICE"].balance -  premium_escrow_contract'["A2B"].balance,
                                                        !["BOB"].balance = wallet["BOB"].balance +  premium_escrow_contract'["A2B"].balance]
                       ELSE /\ TRUE
                            /\ UNCHANGED << premium_escrow_contract, wallet >>
                 /\ UNCHANGED << asset_contract, step_taken >>
      /\ step_considered' = [step_considered EXCEPT ![SAB] = TRUE]
      /\ IF premium_escrow_contract'["A2B"].state>=ACTIVATED /\~step_taken'[SAB]
            THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
            ELSE /\ TRUE
                 /\ UNCHANGED conforming
      /\ pc' = [pc EXCEPT ![A2B] = "SA_BA_ON_AB"]
      /\ UNCHANGED << premium_redeem_contract_sa, path_signature_sa, clock, 
                      ending, party_contract_map >>

SA_BA_ON_AB == /\ pc[A2B] = "SA_BA_ON_AB"
               /\ IF step_taken[SAB]/\step_taken[SSA_A_ON_BA]/\clock<= path_signature_sa["BA_ON_AB"].timeout /\ path_signature_sa["BA_ON_AB"].state=INIT
                     THEN /\ path_signature_sa' = [path_signature_sa EXCEPT !["BA_ON_AB"].state = RELEASED]
                          /\ step_taken' = [step_taken EXCEPT ![SSA_BA_ON_AB] = TRUE]
                          /\ IF asset_contract["A2B"].state = ESCROW
                                THEN /\ asset_contract' = [asset_contract EXCEPT !["A2B"].state = REDEEMED]
                                     /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance + asset_contract'["A2B"].balance,
                                                                 !["ALICE"].balance = wallet["ALICE"].balance - asset_contract'["A2B"].balance]
                                ELSE /\ TRUE
                                     /\ UNCHANGED << asset_contract, wallet >>
                          /\ IF premium_redeem_contract_sa["BA_ON_AB"].state = ESCROW
                                THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["BA_ON_AB"].state = REFUNDED]
                                ELSE /\ TRUE
                                     /\ UNCHANGED premium_redeem_contract_sa
                     ELSE /\ IF step_taken[SAB]/\premium_redeem_contract_sa["BA_ON_AB"].state = ESCROW
                                THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["BA_ON_AB"].state = LOST]
                                     /\ wallet' = [wallet EXCEPT !["ALICE"].balance = wallet["ALICE"].balance + premium_redeem_contract_sa'["BA_ON_AB"].balance,
                                                                 !["BOB"].balance = wallet["BOB"].balance - premium_redeem_contract_sa'["BA_ON_AB"].balance]
                                ELSE /\ TRUE
                                     /\ UNCHANGED << premium_redeem_contract_sa, 
                                                     wallet >>
                          /\ UNCHANGED << asset_contract, path_signature_sa, 
                                          step_taken >>
               /\ step_considered' = [step_considered EXCEPT ![SSA_BA_ON_AB] = TRUE]
               /\ IF ~step_considered'[SSA_A_ON_BA]/\clock<=path_signature_sa'["A_ON_BA"].timeout
                     THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                     ELSE /\ IF step_taken'[SAB]/\step_taken'[SSA_A_ON_BA] /\ ~step_taken'[SSA_BA_ON_AB]
                                THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                                ELSE /\ TRUE
                                     /\ UNCHANGED conforming
               /\ pc' = [pc EXCEPT ![A2B] = "SA_BCA_ON_AB"]
               /\ UNCHANGED << premium_escrow_contract, clock, ending, 
                               party_contract_map >>

SA_BCA_ON_AB == /\ pc[A2B] = "SA_BCA_ON_AB"
                /\ IF step_taken[SAB]/\step_taken[SSA_CA_ON_BC]/\clock<= path_signature_sa["BCA_ON_AB"].timeout /\ path_signature_sa["BCA_ON_AB"].state=INIT
                      THEN /\ path_signature_sa' = [path_signature_sa EXCEPT !["BCA_ON_AB"].state = RELEASED]
                           /\ step_taken' = [step_taken EXCEPT ![SSA_BCA_ON_AB] = TRUE]
                           /\ IF asset_contract["A2B"].state = ESCROW
                                 THEN /\ asset_contract' = [asset_contract EXCEPT !["A2B"].state = REDEEMED]
                                      /\ wallet' = [wallet EXCEPT !["ALICE"].balance = wallet["ALICE"].balance - asset_contract'["A2B"].balance,
                                                                  !["BOB"].balance = wallet["BOB"].balance + asset_contract'["A2B"].balance]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << asset_contract, wallet >>
                           /\ IF premium_redeem_contract_sa["BCA_ON_AB"].state = ESCROW
                                 THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["BCA_ON_AB"].state = REFUNDED]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED premium_redeem_contract_sa
                      ELSE /\ IF asset_contract["A2B"].state = ESCROW
                                 THEN /\ asset_contract' = [asset_contract EXCEPT !["A2B"].state = REFUNDED]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED asset_contract
                           /\ IF premium_redeem_contract_sa["BCA_ON_AB"].state = ESCROW
                                 THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["BCA_ON_AB"].state = LOST]
                                      /\ wallet' = [wallet EXCEPT !["ALICE"].balance = wallet["ALICE"].balance +premium_redeem_contract_sa'["BCA_ON_AB"].balance,
                                                                  !["BOB"].balance = wallet["BOB"].balance - premium_redeem_contract_sa'["BCA_ON_AB"].balance]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << premium_redeem_contract_sa, 
                                                      wallet >>
                           /\ UNCHANGED << path_signature_sa, step_taken >>
                /\ step_considered' = [step_considered EXCEPT ![SSA_BCA_ON_AB] = TRUE]
                /\ IF step_considered'[SSA_CA_ON_BC]/\clock<= path_signature_sa'["CA_ON_BC"].timeout
                      THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                      ELSE /\ IF step_taken'[SAB]/\step_taken'[SSA_CA_ON_BC] /\ ~step_taken'[SSA_BCA_ON_AB]
                                 THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED conforming
                /\ ending' = [ending EXCEPT ![A2B] = TRUE]
                /\ pc' = [pc EXCEPT ![A2B] = "Done"]
                /\ UNCHANGED << premium_escrow_contract, clock, 
                                party_contract_map >>

a2b == P_P_AB \/ P_R_SA_BA_ON_AB \/ P_R_SA_BCA_ON_AB \/ AB \/ SA_BA_ON_AB
          \/ SA_BCA_ON_AB

P_P_BC == /\ pc[B2C] = "P_P_BC"
          /\ IF clock<= premium_escrow_contract["B2C"].deadline /\ premium_escrow_contract["B2C"].state=INIT
                THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["B2C"].state = ESCROW,
                                                                                   !["B2C"].timeout = premium_redeem_contract_sa["CA_ON_BC"].deadline]
                     /\ step_taken' = [step_taken EXCEPT ![SP_P_BC] = TRUE]
                ELSE /\ TRUE
                     /\ UNCHANGED << premium_escrow_contract, step_taken >>
          /\ step_considered' = [step_considered EXCEPT ![SP_P_BC] = TRUE]
          /\ IF ~step_considered'[SP_P_AB] /\ clock<=premium_escrow_contract'["A2B"].deadline
                THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                ELSE /\ IF ~step_taken'[SP_P_AB]/\step_taken'[SP_P_BC]
                           THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                           ELSE /\ IF step_taken'[SP_P_AB]/\~step_taken'[SP_P_BC]
                                      THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED conforming
          /\ pc' = [pc EXCEPT ![B2C] = "P_R_SA_CA_ON_BC"]
          /\ UNCHANGED << asset_contract, premium_redeem_contract_sa, 
                          path_signature_sa, wallet, clock, ending, 
                          party_contract_map >>

P_R_SA_CA_ON_BC == /\ pc[B2C] = "P_R_SA_CA_ON_BC"
                   /\ IF step_taken[SP_P_BC]/\step_taken[SP_R_SA_A_ON_CA]/\clock<= premium_redeem_contract_sa["CA_ON_BC"].deadline /\ premium_redeem_contract_sa["CA_ON_BC"].state=INIT
                         THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["CA_ON_BC"].state = ESCROW,
                                                                                                  !["CA_ON_BC"].timeout = path_signature_sa["CA_ON_BC"].timeout]
                              /\ step_taken' = [step_taken EXCEPT ![SP_R_SA_CA_ON_BC] = TRUE]
                              /\ IF premium_escrow_contract["B2C"].state=ESCROW
                                    THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["B2C"].state = ACTIVATED,
                                                                                                       !["B2C"].timeout = asset_contract["B2C"].deadline]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED premium_escrow_contract
                         ELSE /\ IF premium_escrow_contract["B2C"].state=ESCROW
                                    THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["B2C"].state = REFUNDED]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED premium_escrow_contract
                              /\ UNCHANGED << premium_redeem_contract_sa, 
                                              step_taken >>
                   /\ step_considered' = [step_considered EXCEPT ![SP_R_SA_CA_ON_BC] = TRUE]
                   /\ IF ~step_considered'[SP_R_SA_A_ON_CA]/\clock<=premium_redeem_contract_sa'["A_ON_CA"].deadline
                         THEN /\ conforming' = [conforming EXCEPT !["CAROL"] = FALSE]
                         ELSE /\ IF step_taken'[SP_R_SA_A_ON_CA]/\step_taken'[SP_P_BC]/\~step_taken'[SP_R_SA_CA_ON_BC]
                                    THEN /\ conforming' = [conforming EXCEPT !["CAROL"] = FALSE]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED conforming
                   /\ pc' = [pc EXCEPT ![B2C] = "BC"]
                   /\ UNCHANGED << asset_contract, path_signature_sa, wallet, 
                                   clock, ending, party_contract_map >>

BC == /\ pc[B2C] = "BC"
      /\ IF premium_escrow_contract["B2C"].state=ACTIVATED/\clock<= asset_contract["B2C"].deadline /\ asset_contract["B2C"].state=INIT
            THEN /\ asset_contract' = [asset_contract EXCEPT !["B2C"].state = ESCROW,
                                                             !["B2C"].timeout = path_signature_sa["CA_ON_BC"].timeout]
                 /\ step_taken' = [step_taken EXCEPT ![SBC] = TRUE]
                 /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["B2C"].state = REFUNDED2]
                 /\ UNCHANGED wallet
            ELSE /\ IF premium_escrow_contract["B2C"].state=ACTIVATED
                       THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["B2C"].state = LOST]
                            /\ wallet' = [wallet EXCEPT !["CAROL"].balance = wallet["CAROL"].balance + premium_escrow_contract'["B2C"].balance,
                                                        !["BOB"].balance = wallet["BOB"].balance - premium_escrow_contract'["B2C"].balance]
                       ELSE /\ TRUE
                            /\ UNCHANGED << premium_escrow_contract, wallet >>
                 /\ UNCHANGED << asset_contract, step_taken >>
      /\ step_considered' = [step_considered EXCEPT ![SBC] = TRUE]
      /\ IF ~step_considered'[SAB]/\clock<=asset_contract'["A2B"].deadline
            THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
            ELSE /\ IF step_taken'[SAB]/\premium_escrow_contract'["B2C"].state>=ACTIVATED /\~step_taken'[SBC]
                       THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                       ELSE /\ IF ~step_taken'[SAB]\/step_taken'[SBC]
                                  THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED conforming
      /\ pc' = [pc EXCEPT ![B2C] = "SA_CA_ON_BC"]
      /\ UNCHANGED << premium_redeem_contract_sa, path_signature_sa, clock, 
                      ending, party_contract_map >>

SA_CA_ON_BC == /\ pc[B2C] = "SA_CA_ON_BC"
               /\ IF step_taken[SBC]/\ step_taken[SSA_A_ON_CA]/\clock<= path_signature_sa["CA_ON_BC"].timeout /\ path_signature_sa["CA_ON_BC"].state=INIT
                     THEN /\ path_signature_sa' = [path_signature_sa EXCEPT !["CA_ON_BC"].state = RELEASED]
                          /\ step_taken' = [step_taken EXCEPT ![SSA_CA_ON_BC] = TRUE]
                          /\ IF asset_contract["B2C"].state = ESCROW
                                THEN /\ asset_contract' = [asset_contract EXCEPT !["B2C"].state = REDEEMED]
                                     /\ wallet' = [wallet EXCEPT !["CAROL"].balance = wallet["CAROL"].balance + asset_contract'["B2C"].balance,
                                                                 !["BOB"].balance = wallet["BOB"].balance - asset_contract'["B2C"].balance]
                                ELSE /\ TRUE
                                     /\ UNCHANGED << asset_contract, wallet >>
                          /\ IF premium_redeem_contract_sa["CA_ON_BC"].state = ESCROW
                                THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["CA_ON_BC"].state = REFUNDED]
                                ELSE /\ TRUE
                                     /\ UNCHANGED premium_redeem_contract_sa
                     ELSE /\ IF asset_contract["B2C"].state = ESCROW
                                THEN /\ asset_contract' = [asset_contract EXCEPT !["B2C"].state = REFUNDED]
                                ELSE /\ TRUE
                                     /\ UNCHANGED asset_contract
                          /\ IF step_taken[SBC]/\premium_redeem_contract_sa["CA_ON_BC"].state = ESCROW
                                THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["CA_ON_BC"].state = LOST]
                                     /\ wallet' = [wallet EXCEPT !["CAROL"].balance = wallet["CAROL"].balance - premium_redeem_contract_sa'["CA_ON_BC"].balance,
                                                                 !["BOB"].balance = wallet["BOB"].balance + premium_redeem_contract_sa'["CA_ON_BC"].balance]
                                ELSE /\ TRUE
                                     /\ UNCHANGED << premium_redeem_contract_sa, 
                                                     wallet >>
                          /\ UNCHANGED << path_signature_sa, step_taken >>
               /\ step_considered' = [step_considered EXCEPT ![SSA_CA_ON_BC] = TRUE]
               /\ IF ~step_considered'[SSA_A_ON_CA]/\clock<=path_signature_sa'["A_ON_CA"].timeout
                     THEN /\ conforming' = [conforming EXCEPT !["CAROL"] = FALSE]
                     ELSE /\ IF step_taken'[SBC]/\step_taken'[SSA_A_ON_CA] /\ ~step_taken'[SSA_CA_ON_BC]
                                THEN /\ conforming' = [conforming EXCEPT !["CAROL"] = FALSE]
                                ELSE /\ TRUE
                                     /\ UNCHANGED conforming
               /\ ending' = [ending EXCEPT ![B2C] = TRUE]
               /\ pc' = [pc EXCEPT ![B2C] = "Done"]
               /\ UNCHANGED << premium_escrow_contract, clock, 
                               party_contract_map >>

b2c == P_P_BC \/ P_R_SA_CA_ON_BC \/ BC \/ SA_CA_ON_BC

P_P_CA == /\ pc[C2A] = "P_P_CA"
          /\ IF clock<= premium_escrow_contract["C2A"].deadline /\ premium_escrow_contract["C2A"].state=INIT
                THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["C2A"].state = ESCROW,
                                                                                   !["C2A"].timeout = premium_redeem_contract_sa["A_ON_CA"].deadline]
                     /\ step_taken' = [step_taken EXCEPT ![SP_P_CA] = TRUE]
                ELSE /\ TRUE
                     /\ UNCHANGED << premium_escrow_contract, step_taken >>
          /\ step_considered' = [step_considered EXCEPT ![SP_P_CA] = TRUE]
          /\ IF ~step_considered'[SP_P_BC]/\ clock<=premium_escrow_contract'["B2C"].deadline
                THEN /\ conforming' = [conforming EXCEPT !["CAROL"] = FALSE]
                ELSE /\ IF step_taken'[SP_P_BC]/\~step_taken'[SP_P_CA]
                           THEN /\ conforming' = [conforming EXCEPT !["CAROL"] = FALSE]
                           ELSE /\ IF ~step_taken'[SP_P_BC]/\step_taken'[SP_P_CA]
                                      THEN /\ conforming' = [conforming EXCEPT !["CAROL"] = FALSE]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED conforming
          /\ pc' = [pc EXCEPT ![C2A] = "P_R_SA_A_ON_CA"]
          /\ UNCHANGED << asset_contract, premium_redeem_contract_sa, 
                          path_signature_sa, wallet, clock, ending, 
                          party_contract_map >>

P_R_SA_A_ON_CA == /\ pc[C2A] = "P_R_SA_A_ON_CA"
                  /\ IF step_taken[SP_P_CA]/\clock<= premium_redeem_contract_sa["A_ON_CA"].deadline /\ premium_redeem_contract_sa["A_ON_CA"].state=INIT
                        THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["A_ON_CA"].state = ESCROW,
                                                                                                 !["A_ON_CA"].timeout = path_signature_sa["A_ON_CA"].timeout]
                             /\ step_taken' = [step_taken EXCEPT ![SP_R_SA_A_ON_CA] = TRUE]
                             /\ IF premium_escrow_contract["C2A"].state=ESCROW
                                   THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["C2A"].state = ACTIVATED,
                                                                                                      !["C2A"].timeout = asset_contract["C2A"].deadline]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED premium_escrow_contract
                        ELSE /\ IF premium_escrow_contract["C2A"].state=ESCROW
                                   THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["C2A"].state = REFUNDED]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED premium_escrow_contract
                             /\ UNCHANGED << premium_redeem_contract_sa, 
                                             step_taken >>
                  /\ step_considered' = [step_considered EXCEPT ![SP_R_SA_A_ON_CA] = TRUE]
                  /\ IF ~(step_considered'[SP_P_CA]/\step_considered'[SP_P_BA])\/clock<=premium_escrow_contract'["C2A"].deadline
                        THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                        ELSE /\ IF ~step_taken'[SP_P_BA]/\ step_taken'[SP_R_SA_A_ON_CA]
                                   THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                                   ELSE /\ IF ~step_taken'[SP_P_CA]/\ step_taken'[SP_R_SA_A_ON_CA]
                                              THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                                              ELSE /\ IF step_taken'[SP_P_BA]/\step_taken'[SP_P_CA]/\~step_taken'[SP_R_SA_A_ON_CA]
                                                         THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED conforming
                  /\ pc' = [pc EXCEPT ![C2A] = "CA"]
                  /\ UNCHANGED << asset_contract, path_signature_sa, wallet, 
                                  clock, ending, party_contract_map >>

CA == /\ pc[C2A] = "CA"
      /\ IF premium_escrow_contract["C2A"].state=ACTIVATED/\clock<= asset_contract["C2A"].deadline /\ asset_contract["C2A"].state=INIT
            THEN /\ asset_contract' = [asset_contract EXCEPT !["C2A"].state = ESCROW,
                                                             !["C2A"].timeout = path_signature_sa["A_ON_CA"].timeout]
                 /\ step_taken' = [step_taken EXCEPT ![SCA] = TRUE]
                 /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["C2A"].state = REFUNDED2]
                 /\ UNCHANGED wallet
            ELSE /\ IF premium_escrow_contract["C2A"].state=ACTIVATED
                       THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["C2A"].state = LOST]
                            /\ wallet' = [wallet EXCEPT !["ALICE"].balance = wallet["ALICE"].balance + premium_escrow_contract'["C2A"].balance,
                                                        !["CAROL"].balance = wallet["CAROL"].balance - premium_escrow_contract'["C2A"].balance]
                       ELSE /\ TRUE
                            /\ UNCHANGED << premium_escrow_contract, wallet >>
                 /\ UNCHANGED << asset_contract, step_taken >>
      /\ step_considered' = [step_considered EXCEPT ![SCA] = TRUE]
      /\ IF ~step_considered'[SBC]/\clock<=asset_contract'["B2C"].deadline
            THEN /\ conforming' = [conforming EXCEPT !["CAROL"] = FALSE]
            ELSE /\ IF ~step_taken'[SBC]/\step_taken'[SCA]
                       THEN /\ conforming' = [conforming EXCEPT !["CAROL"] = FALSE]
                       ELSE /\ IF step_taken'[SBC]/\premium_escrow_contract'["C2A"].state>=ACTIVATED /\~step_taken'[SCA]
                                  THEN /\ conforming' = [conforming EXCEPT !["CAROL"] = FALSE]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED conforming
      /\ pc' = [pc EXCEPT ![C2A] = "SA_A_ON_CA"]
      /\ UNCHANGED << premium_redeem_contract_sa, path_signature_sa, clock, 
                      ending, party_contract_map >>

SA_A_ON_CA == /\ pc[C2A] = "SA_A_ON_CA"
              /\ IF step_taken[SCA]/\clock<= path_signature_sa["A_ON_CA"].timeout /\ path_signature_sa["A_ON_CA"].state=INIT
                    THEN /\ path_signature_sa' = [path_signature_sa EXCEPT !["A_ON_CA"].state = RELEASED]
                         /\ step_taken' = [step_taken EXCEPT ![SSA_A_ON_CA] = TRUE]
                         /\ IF asset_contract["C2A"].state = ESCROW
                               THEN /\ asset_contract' = [asset_contract EXCEPT !["C2A"].state = REDEEMED]
                                    /\ wallet' = [wallet EXCEPT !["CAROL"].balance = wallet["CAROL"].balance - asset_contract'["C2A"].balance,
                                                                !["ALICE"].balance = wallet["ALICE"].balance + asset_contract'["C2A"].balance]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << asset_contract, wallet >>
                         /\ IF premium_redeem_contract_sa["A_ON_CA"].state = ESCROW
                               THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["A_ON_CA"].state = REFUNDED]
                               ELSE /\ TRUE
                                    /\ UNCHANGED premium_redeem_contract_sa
                    ELSE /\ IF asset_contract["C2A"].state = ESCROW
                               THEN /\ asset_contract' = [asset_contract EXCEPT !["C2A"].state = REFUNDED]
                               ELSE /\ TRUE
                                    /\ UNCHANGED asset_contract
                         /\ IF step_taken[SCA]/\premium_redeem_contract_sa["A_ON_CA"].state = ESCROW
                               THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["A_ON_CA"].state = LOST]
                                    /\ wallet' = [wallet EXCEPT !["ALICE"].balance = wallet["ALICE"].balance - premium_redeem_contract_sa'["A_ON_CA"].balance,
                                                                !["CAROL"].balance = wallet["CAROL"].balance + premium_redeem_contract_sa'["A_ON_CA"].balance]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << premium_redeem_contract_sa, 
                                                    wallet >>
                         /\ UNCHANGED << path_signature_sa, step_taken >>
              /\ step_considered' = [step_considered EXCEPT ![SSA_A_ON_CA] = TRUE]
              /\ IF ~(step_considered'[SCA]\/step_considered'[SBA])/\clock<=asset_contract'["C2A"].deadline
                    THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                    ELSE /\ IF ~(step_taken'[SCA]/\step_taken'[SBA])/\ step_taken'[SSA_A_ON_CA]
                               THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                               ELSE /\ IF step_taken'[SCA]/\step_taken'[SBA]/\ step_taken'[SAB]/\~step_taken'[SSA_A_ON_CA]
                                          THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED conforming
              /\ ending' = [ending EXCEPT ![C2A] = TRUE]
              /\ pc' = [pc EXCEPT ![C2A] = "Done"]
              /\ UNCHANGED << premium_escrow_contract, clock, 
                              party_contract_map >>

c2a == P_P_CA \/ P_R_SA_A_ON_CA \/ CA \/ SA_A_ON_CA

P_P_BA == /\ pc[B2A] = "P_P_BA"
          /\ IF clock<= premium_escrow_contract["B2A"].deadline /\ premium_escrow_contract["B2A"].state=INIT
                THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["B2A"].state = ESCROW,
                                                                                   !["B2A"].timeout = premium_redeem_contract_sa["A_ON_BA"].deadline]
                     /\ step_taken' = [step_taken EXCEPT ![SP_P_BA] = TRUE]
                ELSE /\ TRUE
                     /\ UNCHANGED << premium_escrow_contract, step_taken >>
          /\ step_considered' = [step_considered EXCEPT ![SP_P_BA] = TRUE]
          /\ IF ~step_considered'[SP_P_AB]/\clock<=premium_escrow_contract'["A2B"].deadline
                THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                ELSE /\ IF step_taken'[SP_P_AB]/\~step_taken'[SP_P_BA]
                           THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                           ELSE /\ IF ~step_taken'[SP_P_AB]/\step_taken'[SP_P_BA]
                                      THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED conforming
          /\ pc' = [pc EXCEPT ![B2A] = "P_R_SA_A_ON_BA"]
          /\ UNCHANGED << asset_contract, premium_redeem_contract_sa, 
                          path_signature_sa, wallet, clock, ending, 
                          party_contract_map >>

P_R_SA_A_ON_BA == /\ pc[B2A] = "P_R_SA_A_ON_BA"
                  /\ IF step_taken[SP_P_BA]/\clock<= premium_redeem_contract_sa["A_ON_BA"].deadline /\ premium_redeem_contract_sa["A_ON_BA"].state=INIT
                        THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["A_ON_BA"].state = ESCROW,
                                                                                                 !["A_ON_BA"].timeout = path_signature_sa["A_ON_BA"].timeout]
                             /\ step_taken' = [step_taken EXCEPT ![SP_R_SA_A_ON_BA] = TRUE]
                             /\ IF premium_escrow_contract["B2A"].state=ESCROW
                                   THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["B2A"].state = ACTIVATED,
                                                                                                      !["B2A"].timeout = asset_contract["B2A"].deadline]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED premium_escrow_contract
                        ELSE /\ IF premium_escrow_contract["B2A"].state=ESCROW
                                   THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["B2A"].state = REFUNDED]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED premium_escrow_contract
                             /\ UNCHANGED << premium_redeem_contract_sa, 
                                             step_taken >>
                  /\ step_considered' = [step_considered EXCEPT ![SP_R_SA_A_ON_BA] = TRUE]
                  /\ IF ~(step_considered'[SP_P_CA]/\step_considered'[SP_P_BA])/\clock<=premium_escrow_contract'["C2A"].deadline
                        THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                        ELSE /\ IF ~step_taken'[SP_P_BA]/\ step_taken'[SP_R_SA_A_ON_BA]
                                   THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                                   ELSE /\ IF ~step_taken'[SP_P_CA]/\step_taken'[SP_R_SA_A_ON_BA]
                                              THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                                              ELSE /\ IF step_taken'[SP_P_BA]/\step_taken'[SP_P_CA]/\~step_taken'[SP_R_SA_A_ON_BA]
                                                         THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED conforming
                  /\ pc' = [pc EXCEPT ![B2A] = "BA"]
                  /\ UNCHANGED << asset_contract, path_signature_sa, wallet, 
                                  clock, ending, party_contract_map >>

BA == /\ pc[B2A] = "BA"
      /\ IF premium_escrow_contract["B2A"].state=ACTIVATED/\clock<= asset_contract["B2A"].deadline /\ asset_contract["B2A"].state=INIT
            THEN /\ asset_contract' = [asset_contract EXCEPT !["B2A"].state = ESCROW,
                                                             !["B2A"].timeout = path_signature_sa["A_ON_BA"].timeout]
                 /\ step_taken' = [step_taken EXCEPT ![SBA] = TRUE]
                 /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["B2A"].state = REFUNDED2]
                 /\ UNCHANGED wallet
            ELSE /\ IF premium_escrow_contract["B2A"].state=ACTIVATED
                       THEN /\ premium_escrow_contract' = [premium_escrow_contract EXCEPT !["B2A"].state = LOST]
                            /\ wallet' = [wallet EXCEPT !["ALICE"].balance = wallet["ALICE"].balance + premium_escrow_contract'["B2C"].balance,
                                                        !["BOB"].balance = wallet["BOB"].balance - premium_escrow_contract'["B2A"].balance]
                       ELSE /\ TRUE
                            /\ UNCHANGED << premium_escrow_contract, wallet >>
                 /\ UNCHANGED << asset_contract, step_taken >>
      /\ step_considered' = [step_considered EXCEPT ![SBA] = TRUE]
      /\ IF ~step_considered'[SAB]/\clock<=asset_contract'["A2B"].deadline
            THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
            ELSE /\ IF step_taken'[SAB]/\premium_escrow_contract'["B2A"].state>=ACTIVATED /\~step_taken'[SBA]
                       THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                       ELSE /\ IF ~step_taken'[SAB]/\step_taken'[SBA]
                                  THEN /\ conforming' = [conforming EXCEPT !["BOB"] = FALSE]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED conforming
      /\ pc' = [pc EXCEPT ![B2A] = "SA_A_ON_BA"]
      /\ UNCHANGED << premium_redeem_contract_sa, path_signature_sa, clock, 
                      ending, party_contract_map >>

SA_A_ON_BA == /\ pc[B2A] = "SA_A_ON_BA"
              /\ IF step_taken[SBA]/\clock<= path_signature_sa["A_ON_BA"].timeout /\ path_signature_sa["A_ON_BA"].state=INIT
                    THEN /\ path_signature_sa' = [path_signature_sa EXCEPT !["A_ON_BA"].state = RELEASED]
                         /\ step_taken' = [step_taken EXCEPT ![SSA_A_ON_BA] = TRUE]
                         /\ IF asset_contract["B2A"].state = ESCROW
                               THEN /\ asset_contract' = [asset_contract EXCEPT !["B2A"].state = REDEEMED]
                                    /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance - asset_contract'["B2A"].balance,
                                                                !["ALICE"].balance = wallet["ALICE"].balance + asset_contract'["B2A"].balance]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << asset_contract, wallet >>
                         /\ IF premium_redeem_contract_sa["A_ON_BA"].state = ESCROW
                               THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["A_ON_BA"].state = REFUNDED]
                               ELSE /\ TRUE
                                    /\ UNCHANGED premium_redeem_contract_sa
                    ELSE /\ IF asset_contract["B2A"].state = ESCROW
                               THEN /\ asset_contract' = [asset_contract EXCEPT !["B2A"].state = REFUNDED]
                               ELSE /\ TRUE
                                    /\ UNCHANGED asset_contract
                         /\ IF step_taken[SBA]/\premium_redeem_contract_sa["A_ON_BA"].state = ESCROW
                               THEN /\ premium_redeem_contract_sa' = [premium_redeem_contract_sa EXCEPT !["A_ON_BA"].state = LOST]
                                    /\ wallet' = [wallet EXCEPT !["ALICE"].balance = wallet["ALICE"].balance - premium_redeem_contract_sa'["A_ON_BA"].balance,
                                                                !["BOB"].balance = wallet["BOB"].balance + premium_redeem_contract_sa'["A_ON_BA"].balance]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << premium_redeem_contract_sa, 
                                                    wallet >>
                         /\ UNCHANGED << path_signature_sa, step_taken >>
              /\ step_considered' = [step_considered EXCEPT ![SSA_A_ON_BA] = TRUE]
              /\ IF ~(step_considered'[SCA]/\step_considered'[SBA])/\clock<=asset_contract'["C2A"].deadline
                    THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                    ELSE /\ IF step_taken'[SCA]/\step_taken'[SBA]/\ ~step_taken'[SSA_A_ON_BA]
                               THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                               ELSE /\ IF ~(step_taken'[SCA]/\step_taken'[SBA])/\ step_taken'[SSA_A_ON_BA]
                                          THEN /\ conforming' = [conforming EXCEPT !["ALICE"] = FALSE]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED conforming
              /\ ending' = [ending EXCEPT ![B2A] = TRUE]
              /\ pc' = [pc EXCEPT ![B2A] = "Done"]
              /\ UNCHANGED << premium_escrow_contract, clock, 
                              party_contract_map >>

b2a == P_P_BA \/ P_R_SA_A_ON_BA \/ BA \/ SA_A_ON_BA

tick == /\ pc[CLOCK] = "tick"
        /\ IF (clock <LIMIT)
              THEN /\ pc' = [pc EXCEPT ![CLOCK] = "tok"]
              ELSE /\ pc' = [pc EXCEPT ![CLOCK] = "Done"]
        /\ UNCHANGED << asset_contract, premium_escrow_contract, 
                        premium_redeem_contract_sa, path_signature_sa, wallet, 
                        clock, step_considered, conforming, step_taken, ending, 
                        party_contract_map >>

tok == /\ pc[CLOCK] = "tok"
       /\ clock' = clock + 1
       /\ pc' = [pc EXCEPT ![CLOCK] = "tick"]
       /\ UNCHANGED << asset_contract, premium_escrow_contract, 
                       premium_redeem_contract_sa, path_signature_sa, wallet, 
                       step_considered, conforming, step_taken, ending, 
                       party_contract_map >>

Clock == tick \/ tok

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == a2b \/ b2c \/ c2a \/ b2a \/ Clock
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a2b)
        /\ WF_vars(b2c)
        /\ WF_vars(c2a)
        /\ WF_vars(b2a)
        /\ WF_vars(Clock)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-22754b5f0810a34cc15d599a99239ea8
====
