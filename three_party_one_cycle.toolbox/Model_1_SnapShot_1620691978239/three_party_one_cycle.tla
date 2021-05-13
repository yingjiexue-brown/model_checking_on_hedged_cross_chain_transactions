 ------------------------- MODULE three_party_one_cycle-------------------------

EXTENDS Integers, TLC
(* --algorithm example

variables
(*
Protocol description:
Three-party-swap: Goal: Alice(leader) pays 100$ BTC to Bob, 
                   Bob pays 100$ LTC to carol, 
                   Carol  pays $100 ether to Alice (The order does not matter.  )
Procedures: (deposit premiums: A->C->B)
            clock=0: Alice deposits $3 on Ethereum blockchain; 
            clock=1: Carol deposits $2 on LTC blockchain;
            clock=2: Bob deposits $1 on Bitcoin blockchain;
            (escrow 100$ coins)
            clock=3: Alice escrows $100 BTC;
            clock =4: Bob escrows $100 LTC;
            clock =5: Carol escrows $100 Ether;
            (redeem phase)
            clock =6: Alice redeems ether;
            clock =7: Carol redeems LTC;
            clock =8: Bob redeems BTC;
            
Overview of the simulation:
Roughly speaking, we are simulating all possible permutations of those 9 steps, each step can happen according to the protocol or skip;
           

*)
    \* An asset_contract has balance, timeout is initialized as -1 and it will be changed after it is escrowed;
    \* a deadline to be escrowed
    asset_contract = [ALICE |-> [balance |->100, timeout |-> -1, state |-> INIT,deadline |-> 3, timestamp |-> LIMIT],
                BOB|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 4, timestamp |-> LIMIT],
                CAROL|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 5, timestamp |-> LIMIT]],
    \* A premium asset_contract has balance, timeout is initialized as -1 and it will be changed after it is escrowed; 
    \* a deadline to escrow it
    \* the party denotes who is responsible to deposit premiums
    premium_contract = [ALICE |-> [balance|->3, timeout |-> -1, state |-> INIT,deadline |-> 0, timestamp |-> LIMIT],
               BOB|->[balance|->1, timeout |->-1, state |-> INIT,deadline |-> 2, timestamp |-> LIMIT],
               CAROL|->[balance|->2, timeout |->-1, state |-> INIT,deadline |-> 1, timestamp |-> LIMIT]],
               
    wallet = [ALICE |-> [balance|->103,init|->103], BOB|-> [balance|->101,init|->101],CAROL |->[balance|->102,init|->102]],
    hashkey = [C2A|->[deadline|->6,state|->INIT],B2C|->[deadline|->7,state|->INIT],A2B|->[deadline|->8,state|->INIT]],
    \* global clock
    clock = 0,
    \* indicating whether a step is considered in the model
    step_considered = [s \in STEPS |->FALSE],
    conforming = [p \in  PARTIES |->TRUE],
    step_taken = [s \in STEPS |->FALSE],

define
 INIT == 0 ESCROW == 1 REDEEMED == 2 REFUNDED == 3 LOST ==4 EXPIRED == 5 \* contract states
 ALICE == 0 BOB == 1 CAROL ==2  \* ID for parties
 BITCOIN == 0 LITECOIN ==1 ETHER ==2 CLOCK == 3    \* process ids
 LIMIT == 9                         \* max clock value
 PARTIES == {ALICE, BOB, CAROL}            \* parties
 A_D_P == 0  C_D_P == 1 B_D_P ==2 A_E==3 B_E==4 C_E==5 
 A_R==6 C_R==7 B_R==8 \* step index
 
 STEPS == {A_D_P, B_D_P,C_D_P,A_E,B_E,C_E, A_R,B_R,C_R} 
 \* properties that we want to check
 ending == /\ step_considered[A_R]/\step_considered[B_R]/\step_considered[C_R]
 liveness_pre ==/\ending/\conforming[ALICE]/\conforming[BOB]/\conforming[CAROL]\* helper
 liveness == (liveness_pre) =>(/\premium_contract["ALICE"].state=REFUNDED /\premium_contract["BOB"].state=REFUNDED/\premium_contract["CAROL"].state=REFUNDED/\asset_contract["ALICE"].state=REDEEMED /\asset_contract["BOB"].state=REDEEMED/\asset_contract["CAROL"].state=REDEEMED)
 compensated_alice == (/\ending/\conforming[ALICE]/\asset_contract["ALICE"].state=REFUNDED) => wallet["ALICE"].balance>=wallet["ALICE"].init+1
 compensated_bob == (/\ending/\conforming[BOB]/\asset_contract["BOB"].state=REFUNDED) => wallet["BOB"].balance>=wallet["BOB"].init+1
 compensated_carol == (/\ending/\conforming[CAROL]/\asset_contract["CAROL"].state=REFUNDED) => wallet["CAROL"].balance>=wallet["CAROL"].init+1
 safe_alice == (/\ending/\conforming[ALICE]) => wallet["ALICE"].balance>=wallet["ALICE"].init
 safe_bob == (/\ending/\conforming[BOB]) => wallet["BOB"].balance>=wallet["BOB"].init
 safe_carol == (/\ending/\conforming[CAROL]) => wallet["CAROL"].balance>=wallet["CAROL"].init
 
 
end define;

\* Bitcoin process (A2B) =======================================================================================================
fair process bitcoin = BITCOIN begin 

S_B_D_P: \*clock =2, BOB deposits his premium
    
    if clock<= premium_contract["BOB"].deadline /\ premium_contract["BOB"].state=INIT then \*otherwise, Bob can do nothing
       premium_contract["BOB"].state:=ESCROW 
              || premium_contract["BOB"].timestamp:=clock
              ||premium_contract["BOB"].timeout:=asset_contract["ALICE"].deadline;\* Bob deposits a premium on A2B
              step_taken[B_D_P]:= TRUE;
    end if;
    
    if ~step_considered[C_D_P] /\ clock<=premium_contract["CAROL"].deadline then
       conforming[BOB]:=FALSE;
     elsif ~step_taken[C_D_P]/\step_taken[B_D_P] then \* if alice does not deposit premium_contracts, carol deposits hers, carol is crazy
       conforming[BOB]:=FALSE;
     elsif step_taken[C_D_P]/\~step_taken[B_D_P] then \* if alice  deposits premiums, carol does not deposit hers, carol is non-conforming                                        \* Todo: what if bob deposits his premium ealier?
        conforming[BOB]:=FALSE;
    end if;
    step_considered[B_D_P]:=TRUE;

    

S_A_E:\*clock =3, Alice escrows her asset

    if step_taken[B_D_P] /\ clock <= asset_contract["ALICE"].deadline /\  asset_contract["ALICE"].state = INIT then \*if DP2 finishes, Alice can choose to escrow her swap asset_contract or not
           asset_contract["ALICE"].state := ESCROW
           ||asset_contract["ALICE"].timestamp := clock
           ||asset_contract["ALICE"].timeout := hashkey["A2B"].deadline; 
           step_taken[A_E]:= TRUE;
       
    elsif  premium_contract["BOB"].state=ESCROW then \* if Alice cannot escrow her contract, then the premium being escrowed should be refunded
           premium_contract["BOB"].state:=REFUNDED 
    end if;
    
     if ~step_considered[B_D_P] /\ clock<=premium_contract["BOB"].deadline then
        conforming[ALICE]:=FALSE;
    elsif ~step_taken[B_D_P]/\step_taken[A_E]then  \* the precondition for alice to escrow her asset
     conforming[ALICE]:=FALSE;
    elsif step_taken[B_D_P]/\~step_taken[A_E] then 
     conforming[ALICE]:=FALSE;
    end if;
    step_considered[A_E]:=TRUE;
   

S_B_R:\* clock =8,Bob redeems
    if  step_taken[A_E]/\clock<=asset_contract["ALICE"].timeout/\ asset_contract["ALICE"].state= ESCROW then
        asset_contract["ALICE"].state:= REDEEMED;
        if premium_contract["BOB"].state = ESCROW then
        premium_contract["BOB"].state:=REFUNDED;
        end if;
        wallet["BOB"].balance:=wallet["BOB"].balance+asset_contract["ALICE"].balance
        ||wallet["ALICE"].balance:=wallet["ALICE"].balance-asset_contract["ALICE"].balance;
        step_taken[B_R]:= TRUE;
        
    elsif step_taken[A_E]/\ asset_contract["ALICE"].state= ESCROW then
         asset_contract["ALICE"].state := REFUNDED;
            if premium_contract["BOB"].state = ESCROW then
         premium_contract["BOB"].state:=LOST;
         wallet["BOB"].balance := wallet["BOB"].balance-premium_contract["BOB"].balance
         ||wallet["ALICE"].balance := wallet["ALICE"].balance+premium_contract["BOB"].balance;
         end if;
    end if;
  
    if ~(asset_contract["BOB"].state= REDEEMED)/\(asset_contract["CAROL"].state= REDEEMED)/\step_taken[B_R] then
      conforming[CAROL]:=FALSE;
    elsif ~(asset_contract["CAROL"].state= REDEEMED)/\step_taken[B_R] then
      conforming[ALICE]:=FALSE;
    elsif ~step_considered[C_R]/\clock<= hashkey["B2C"].deadline then
       conforming[BOB]:=FALSE;
    elsif step_taken[C_R]/\step_taken[A_E]/\~step_taken[B_R] then
        conforming[BOB]:=FALSE;
    end if;
  
    step_considered[B_R]:=TRUE;
end process

\* Litecoin process (B2C)=======================================================================================================
fair process litecoin=LITECOIN begin

S_C_D_P:\*clock =1, carol deposits her premium_contract
    if clock<=premium_contract["CAROL"].deadline /\ premium_contract["CAROL"].state=INIT then 
         premium_contract["CAROL"].timestamp:=clock 
               || premium_contract["CAROL"].state:=ESCROW
               ||premium_contract["CAROL"].timeout:=asset_contract["BOB"].deadline;\* Carol deposits a premium on B2C
               step_taken[C_D_P]:= TRUE;
    end if;
    
     if ~step_considered[A_D_P] /\ clock<=premium_contract["ALICE"].deadline then
       conforming[CAROL]:=FALSE;
     elsif ~step_taken[A_D_P]/\step_taken[C_D_P] then \* if alice does not deposit premiums, carol deposits hers, carol is crazy
       conforming[CAROL]:=FALSE;
     elsif step_taken[A_D_P]/\~step_taken[C_D_P] then \* if alice  deposits premiums, carol does not deposit hers, carol is non-conforming                                        \* Todo: what if bob deposits his premium_contract ealier?
       conforming[CAROL]:=FALSE;
    end if;
    step_considered[C_D_P]:=TRUE;
  

S_B_E:\*clock =4, Bob escrows his asset
    if step_taken[C_D_P] /\ clock<=asset_contract["BOB"].deadline /\ asset_contract["BOB"].state = INIT then
                 asset_contract["BOB"].state := ESCROW
                ||asset_contract["BOB"].timestamp := clock
                ||asset_contract["BOB"].timeout:=hashkey["B2C"].deadline; 
                step_taken[B_E]:=TRUE;
       
    elsif premium_contract["CAROL"].state=ESCROW then
          premium_contract["CAROL"].state:=REFUNDED;
    end if;
    
    if ~step_considered[A_E] /\ clock<=asset_contract["ALICE"].deadline then
       conforming[BOB]:=FALSE;
    elsif step_taken[A_E]/\step_taken[C_D_P]/\~step_taken[B_E]then
       conforming[BOB]:=FALSE;
    elsif ~step_taken[A_E]/\step_taken[B_E]then
     conforming[BOB]:=FALSE;
    end if;
    
    step_considered[B_E]:=TRUE;
    
  
    
    
S_C_R:\*clock =7, carol redeems
    if step_taken[B_E]/\clock<=asset_contract["BOB"].timeout /\ asset_contract["BOB"].state = ESCROW then
               asset_contract["BOB"].state := REDEEMED;
               if   premium_contract["CAROL"].state=ESCROW then
               premium_contract["CAROL"].state:=REFUNDED;
               end if;
               wallet["BOB"].balance := wallet["BOB"].balance-asset_contract["BOB"].balance
               ||wallet["CAROL"].balance := wallet["CAROL"].balance+asset_contract["BOB"].balance;
               step_taken[C_R]:=TRUE;
      
    elsif step_taken[B_E] /\ asset_contract["BOB"].state = ESCROW then 
           asset_contract["BOB"].state := REFUNDED;
           if   premium_contract["CAROL"].state=ESCROW then
           premium_contract["CAROL"].state:=LOST;
           wallet["BOB"].balance := wallet["BOB"].balance+premium_contract["CAROL"].balance
           ||wallet["CAROL"].balance := wallet["CAROL"].balance-premium_contract["CAROL"].balance
           end if;
    end if;
    if  ~(asset_contract["CAROL"].state= REDEEMED)/\step_taken[C_R] then
         conforming[ALICE]:=FALSE;
    elsif ~step_considered[A_R] /\ clock<= hashkey["C2A"].deadline then
       conforming[CAROL]:=FALSE;
    elsif step_taken[A_R]/\step_taken[B_E]/\~step_taken[C_R]then
        conforming[CAROL]:=FALSE;
    end if;
    step_considered[C_R]:=TRUE;
end process

\* Ether process: C2A =======================================================================================================

fair process ether=ETHER begin

S_A_D_P:\* clock =0 ,Alice deposits her premium in Ether
    if clock<=premium_contract["ALICE"].deadline /\ premium_contract["ALICE"].state=INIT then \*otherwise, Alice cannot escrow
               premium_contract["ALICE"].timestamp:=clock 
               || premium_contract["ALICE"].state:=ESCROW
               ||premium_contract["ALICE"].timeout:=asset_contract["CAROL"].deadline; \* Alice deposits a premium on C2A
               step_taken[A_D_P]:= TRUE;
        
    end if;
    
    if ~step_taken[A_D_P] then
       conforming[ALICE]:=FALSE;
    end if;
    
    step_considered[A_D_P]:=TRUE;
 

S_C_E:\*clock =5, Carol escrows her asset
    if step_taken[A_D_P] /\ clock<=asset_contract["CAROL"].deadline /\asset_contract["CAROL"].state =INIT then
                 asset_contract["CAROL"].state := ESCROW
                ||asset_contract["CAROL"].timestamp := clock
                ||asset_contract["CAROL"].timeout:=hashkey["C2A"].deadline;
                step_taken[C_E]:=TRUE;
        
    elsif premium_contract["ALICE"].state=ESCROW then
          premium_contract["ALICE"].state:=REFUNDED;
       
    end if;
   
    if ~step_considered[B_E]/\ clock<=asset_contract["BOB"].deadline then 
    conforming[CAROL]:=FALSE;
    elsif ~step_taken[B_E]/\step_taken[C_E]then
     conforming[CAROL]:=FALSE;
    elsif step_taken[B_E]/\step_taken[A_D_P]/\~step_taken[C_E]then
     conforming[CAROL]:=FALSE;
    end if;
    
    step_considered[C_E]:=TRUE;
 

S_A_R:\*clock =6, Alice redeems
    
    if step_taken[C_E]/\clock<=asset_contract["CAROL"].timeout/\asset_contract["CAROL"].state = ESCROW then
                asset_contract["CAROL"].state := REDEEMED;
               if premium_contract["ALICE"].state = ESCROW then
                   premium_contract["ALICE"].state:=REFUNDED;
               end if;
               wallet["CAROL"].balance := wallet["CAROL"].balance-asset_contract["CAROL"].balance
               ||wallet["ALICE"].balance := wallet["ALICE"].balance+asset_contract["CAROL"].balance;
               step_taken[A_R]:=TRUE;
       
    elsif step_taken[C_E] /\asset_contract["CAROL"].state = ESCROW then \* Alice is too late
           asset_contract["CAROL"].state := REFUNDED;
           if premium_contract["ALICE"].state = ESCROW then
           premium_contract["ALICE"].state:=LOST;
           wallet["CAROL"].balance := wallet["CAROL"].balance+premium_contract["ALICE"].balance
           ||wallet["ALICE"].balance := wallet["ALICE"].balance-premium_contract["ALICE"].balance
           end if;
    end if;
   
   
    if ~step_considered[C_E]/\ clock<=asset_contract["CAROL"].deadline then
     conforming[ALICE]:=FALSE;
    elsif step_taken[C_E]/\~step_taken[A_R] then 
      conforming[ALICE]:=FALSE;
    elsif ~step_taken[C_E]/\step_taken[A_R] then 
      conforming[ALICE]:=FALSE;
    end if;
    step_considered[A_R]:=TRUE;
end process

\* clock tick process =======================================================================================================
fair process Clock = CLOCK begin tick:
    while (clock <LIMIT) do
    tok: clock := clock + 1;
    end while;
 end process
 

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ba1a9f19d367552c41f193257eea968b
VARIABLES asset_contract, premium_contract, wallet, hashkey, clock, 
          step_considered, conforming, step_taken, pc

(* define statement *)
INIT == 0 ESCROW == 1 REDEEMED == 2 REFUNDED == 3 LOST ==4 EXPIRED == 5
ALICE == 0 BOB == 1 CAROL ==2
BITCOIN == 0 LITECOIN ==1 ETHER ==2 CLOCK == 3
LIMIT == 9
PARTIES == {ALICE, BOB, CAROL}
A_D_P == 0  C_D_P == 1 B_D_P ==2 A_E==3 B_E==4 C_E==5
A_R==6 C_R==7 B_R==8

STEPS == {A_D_P, B_D_P,C_D_P,A_E,B_E,C_E, A_R,B_R,C_R}

ending == /\ step_considered[A_R]/\step_considered[B_R]/\step_considered[C_R]
liveness_pre ==/\ending/\conforming[ALICE]/\conforming[BOB]/\conforming[CAROL]
liveness == (liveness_pre) =>(/\premium_contract["ALICE"].state=REFUNDED /\premium_contract["BOB"].state=REFUNDED/\premium_contract["CAROL"].state=REFUNDED/\asset_contract["ALICE"].state=REDEEMED /\asset_contract["BOB"].state=REDEEMED/\asset_contract["CAROL"].state=REDEEMED)
compensated_alice == (/\ending/\conforming[ALICE]/\asset_contract["ALICE"].state=REFUNDED) => wallet["ALICE"].balance>=wallet["ALICE"].init+1
compensated_bob == (/\ending/\conforming[BOB]/\asset_contract["BOB"].state=REFUNDED) => wallet["BOB"].balance>=wallet["BOB"].init+1
compensated_carol == (/\ending/\conforming[CAROL]/\asset_contract["CAROL"].state=REFUNDED) => wallet["CAROL"].balance>=wallet["CAROL"].init+1
safe_alice == (/\ending/\conforming[ALICE]) => wallet["ALICE"].balance>=wallet["ALICE"].init
safe_bob == (/\ending/\conforming[BOB]) => wallet["BOB"].balance>=wallet["BOB"].init
safe_carol == (/\ending/\conforming[CAROL]) => wallet["CAROL"].balance>=wallet["CAROL"].init


vars == << asset_contract, premium_contract, wallet, hashkey, clock, 
           step_considered, conforming, step_taken, pc >>

ProcSet == {BITCOIN} \cup {LITECOIN} \cup {ETHER} \cup {CLOCK}

Init == (* Global variables *)
        /\ asset_contract =      [ALICE |-> [balance |->100, timeout |-> -1, state |-> INIT,deadline |-> 3, timestamp |-> LIMIT],
                            BOB|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 4, timestamp |-> LIMIT],
                            CAROL|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 5, timestamp |-> LIMIT]]
        /\ premium_contract =         [ALICE |-> [balance|->3, timeout |-> -1, state |-> INIT,deadline |-> 0, timestamp |-> LIMIT],
                              BOB|->[balance|->1, timeout |->-1, state |-> INIT,deadline |-> 2, timestamp |-> LIMIT],
                              CAROL|->[balance|->2, timeout |->-1, state |-> INIT,deadline |-> 1, timestamp |-> LIMIT]]
        /\ wallet = [ALICE |-> [balance|->103,init|->103], BOB|-> [balance|->101,init|->101],CAROL |->[balance|->102,init|->102]]
        /\ hashkey = [C2A|->[deadline|->6,state|->INIT],B2C|->[deadline|->7,state|->INIT],A2B|->[deadline|->8,state|->INIT]]
        /\ clock = 0
        /\ step_considered = [s \in STEPS |->FALSE]
        /\ conforming = [p \in  PARTIES |->TRUE]
        /\ step_taken = [s \in STEPS |->FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = BITCOIN -> "S_B_D_P"
                                        [] self = LITECOIN -> "S_C_D_P"
                                        [] self = ETHER -> "S_A_D_P"
                                        [] self = CLOCK -> "tick"]

S_B_D_P == /\ pc[BITCOIN] = "S_B_D_P"
           /\ IF clock<= premium_contract["BOB"].deadline /\ premium_contract["BOB"].state=INIT
                 THEN /\ premium_contract' = [premium_contract EXCEPT !["BOB"].state = ESCROW,
                                                                      !["BOB"].timestamp = clock,
                                                                      !["BOB"].timeout = asset_contract["ALICE"].deadline]
                      /\ step_taken' = [step_taken EXCEPT ![B_D_P] = TRUE]
                 ELSE /\ TRUE
                      /\ UNCHANGED << premium_contract, step_taken >>
           /\ IF ~step_considered[C_D_P] /\ clock<=premium_contract'["CAROL"].deadline
                 THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                 ELSE /\ IF ~step_taken'[C_D_P]/\step_taken'[B_D_P]
                            THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                            ELSE /\ IF step_taken'[C_D_P]/\~step_taken'[B_D_P]
                                       THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED conforming
           /\ step_considered' = [step_considered EXCEPT ![B_D_P] = TRUE]
           /\ pc' = [pc EXCEPT ![BITCOIN] = "S_A_E"]
           /\ UNCHANGED << asset_contract, wallet, hashkey, clock >>

S_A_E == /\ pc[BITCOIN] = "S_A_E"
         /\ IF step_taken[B_D_P] /\ clock <= asset_contract["ALICE"].deadline /\  asset_contract["ALICE"].state = INIT
               THEN /\ asset_contract' = [asset_contract EXCEPT !["ALICE"].state = ESCROW,
                                                                !["ALICE"].timestamp = clock,
                                                                !["ALICE"].timeout = hashkey["A2B"].deadline]
                    /\ step_taken' = [step_taken EXCEPT ![A_E] = TRUE]
                    /\ UNCHANGED premium_contract
               ELSE /\ IF premium_contract["BOB"].state=ESCROW
                          THEN /\ premium_contract' = [premium_contract EXCEPT !["BOB"].state = REFUNDED]
                          ELSE /\ TRUE
                               /\ UNCHANGED premium_contract
                    /\ UNCHANGED << asset_contract, step_taken >>
         /\ IF ~step_considered[B_D_P] /\ clock<=premium_contract'["BOB"].deadline
               THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
               ELSE /\ IF ~step_taken'[B_D_P]/\step_taken'[A_E]
                          THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                          ELSE /\ IF step_taken'[B_D_P]/\~step_taken'[A_E]
                                     THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED conforming
         /\ step_considered' = [step_considered EXCEPT ![A_E] = TRUE]
         /\ pc' = [pc EXCEPT ![BITCOIN] = "S_B_R"]
         /\ UNCHANGED << wallet, hashkey, clock >>

S_B_R == /\ pc[BITCOIN] = "S_B_R"
         /\ IF step_taken[A_E]/\clock<=asset_contract["ALICE"].timeout/\ asset_contract["ALICE"].state= ESCROW
               THEN /\ asset_contract' = [asset_contract EXCEPT !["ALICE"].state = REDEEMED]
                    /\ IF premium_contract["BOB"].state = ESCROW
                          THEN /\ premium_contract' = [premium_contract EXCEPT !["BOB"].state = REFUNDED]
                          ELSE /\ TRUE
                               /\ UNCHANGED premium_contract
                    /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance+asset_contract'["ALICE"].balance,
                                                !["ALICE"].balance = wallet["ALICE"].balance-asset_contract'["ALICE"].balance]
                    /\ step_taken' = [step_taken EXCEPT ![B_R] = TRUE]
               ELSE /\ IF step_taken[A_E]/\ asset_contract["ALICE"].state= ESCROW
                          THEN /\ asset_contract' = [asset_contract EXCEPT !["ALICE"].state = REFUNDED]
                               /\ IF premium_contract["BOB"].state = ESCROW
                                     THEN /\ premium_contract' = [premium_contract EXCEPT !["BOB"].state = LOST]
                                          /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance-premium_contract'["BOB"].balance,
                                                                      !["ALICE"].balance = wallet["ALICE"].balance+premium_contract'["BOB"].balance]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << premium_contract, 
                                                          wallet >>
                          ELSE /\ TRUE
                               /\ UNCHANGED << asset_contract, 
                                               premium_contract, wallet >>
                    /\ UNCHANGED step_taken
         /\ IF ~(asset_contract'["BOB"].state= REDEEMED)/\(asset_contract'["CAROL"].state= REDEEMED)/\step_taken'[B_R]
               THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
               ELSE /\ IF ~(asset_contract'["CAROL"].state= REDEEMED)/\step_taken'[B_R]
                          THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                          ELSE /\ IF ~step_considered[C_R]/\clock<= hashkey["B2C"].deadline
                                     THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                                     ELSE /\ IF step_taken'[C_R]/\step_taken'[A_E]/\~step_taken'[B_R]
                                                THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED conforming
         /\ step_considered' = [step_considered EXCEPT ![B_R] = TRUE]
         /\ pc' = [pc EXCEPT ![BITCOIN] = "Done"]
         /\ UNCHANGED << hashkey, clock >>

bitcoin == S_B_D_P \/ S_A_E \/ S_B_R

S_C_D_P == /\ pc[LITECOIN] = "S_C_D_P"
           /\ IF clock<=premium_contract["CAROL"].deadline /\ premium_contract["CAROL"].state=INIT
                 THEN /\ premium_contract' = [premium_contract EXCEPT !["CAROL"].timestamp = clock,
                                                                      !["CAROL"].state = ESCROW,
                                                                      !["CAROL"].timeout = asset_contract["BOB"].deadline]
                      /\ step_taken' = [step_taken EXCEPT ![C_D_P] = TRUE]
                 ELSE /\ TRUE
                      /\ UNCHANGED << premium_contract, step_taken >>
           /\ IF ~step_considered[A_D_P] /\ clock<=premium_contract'["ALICE"].deadline
                 THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
                 ELSE /\ IF ~step_taken'[A_D_P]/\step_taken'[C_D_P]
                            THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
                            ELSE /\ IF step_taken'[A_D_P]/\~step_taken'[C_D_P]
                                       THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED conforming
           /\ step_considered' = [step_considered EXCEPT ![C_D_P] = TRUE]
           /\ pc' = [pc EXCEPT ![LITECOIN] = "S_B_E"]
           /\ UNCHANGED << asset_contract, wallet, hashkey, clock >>

S_B_E == /\ pc[LITECOIN] = "S_B_E"
         /\ IF step_taken[C_D_P] /\ clock<=asset_contract["BOB"].deadline /\ asset_contract["BOB"].state = INIT
               THEN /\ asset_contract' = [asset_contract EXCEPT !["BOB"].state = ESCROW,
                                                                !["BOB"].timestamp = clock,
                                                                !["BOB"].timeout = hashkey["B2C"].deadline]
                    /\ step_taken' = [step_taken EXCEPT ![B_E] = TRUE]
                    /\ UNCHANGED premium_contract
               ELSE /\ IF premium_contract["CAROL"].state=ESCROW
                          THEN /\ premium_contract' = [premium_contract EXCEPT !["CAROL"].state = REFUNDED]
                          ELSE /\ TRUE
                               /\ UNCHANGED premium_contract
                    /\ UNCHANGED << asset_contract, step_taken >>
         /\ IF ~step_considered[A_E] /\ clock<=asset_contract'["ALICE"].deadline
               THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
               ELSE /\ IF step_taken'[A_E]/\step_taken'[C_D_P]/\~step_taken'[B_E]
                          THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                          ELSE /\ IF ~step_taken'[A_E]/\step_taken'[B_E]
                                     THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED conforming
         /\ step_considered' = [step_considered EXCEPT ![B_E] = TRUE]
         /\ pc' = [pc EXCEPT ![LITECOIN] = "S_C_R"]
         /\ UNCHANGED << wallet, hashkey, clock >>

S_C_R == /\ pc[LITECOIN] = "S_C_R"
         /\ IF step_taken[B_E]/\clock<=asset_contract["BOB"].timeout /\ asset_contract["BOB"].state = ESCROW
               THEN /\ asset_contract' = [asset_contract EXCEPT !["BOB"].state = REDEEMED]
                    /\ IF premium_contract["CAROL"].state=ESCROW
                          THEN /\ premium_contract' = [premium_contract EXCEPT !["CAROL"].state = REFUNDED]
                          ELSE /\ TRUE
                               /\ UNCHANGED premium_contract
                    /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance-asset_contract'["BOB"].balance,
                                                !["CAROL"].balance = wallet["CAROL"].balance+asset_contract'["BOB"].balance]
                    /\ step_taken' = [step_taken EXCEPT ![C_R] = TRUE]
               ELSE /\ IF step_taken[B_E] /\ asset_contract["BOB"].state = ESCROW
                          THEN /\ asset_contract' = [asset_contract EXCEPT !["BOB"].state = REFUNDED]
                               /\ IF premium_contract["CAROL"].state=ESCROW
                                     THEN /\ premium_contract' = [premium_contract EXCEPT !["CAROL"].state = LOST]
                                          /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance+premium_contract'["CAROL"].balance,
                                                                      !["CAROL"].balance = wallet["CAROL"].balance-premium_contract'["CAROL"].balance]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << premium_contract, 
                                                          wallet >>
                          ELSE /\ TRUE
                               /\ UNCHANGED << asset_contract, 
                                               premium_contract, wallet >>
                    /\ UNCHANGED step_taken
         /\ IF ~(asset_contract'["CAROL"].state= REDEEMED)/\step_taken'[C_R]
               THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
               ELSE /\ IF ~step_considered[A_R] /\ clock<= hashkey["C2A"].deadline
                          THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
                          ELSE /\ IF step_taken'[A_R]/\step_taken'[B_E]/\~step_taken'[C_R]
                                     THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED conforming
         /\ step_considered' = [step_considered EXCEPT ![C_R] = TRUE]
         /\ pc' = [pc EXCEPT ![LITECOIN] = "Done"]
         /\ UNCHANGED << hashkey, clock >>

litecoin == S_C_D_P \/ S_B_E \/ S_C_R

S_A_D_P == /\ pc[ETHER] = "S_A_D_P"
           /\ IF clock<=premium_contract["ALICE"].deadline /\ premium_contract["ALICE"].state=INIT
                 THEN /\ premium_contract' = [premium_contract EXCEPT !["ALICE"].timestamp = clock,
                                                                      !["ALICE"].state = ESCROW,
                                                                      !["ALICE"].timeout = asset_contract["CAROL"].deadline]
                      /\ step_taken' = [step_taken EXCEPT ![A_D_P] = TRUE]
                 ELSE /\ TRUE
                      /\ UNCHANGED << premium_contract, step_taken >>
           /\ IF ~step_taken'[A_D_P]
                 THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                 ELSE /\ TRUE
                      /\ UNCHANGED conforming
           /\ step_considered' = [step_considered EXCEPT ![A_D_P] = TRUE]
           /\ pc' = [pc EXCEPT ![ETHER] = "S_C_E"]
           /\ UNCHANGED << asset_contract, wallet, hashkey, clock >>

S_C_E == /\ pc[ETHER] = "S_C_E"
         /\ IF step_taken[A_D_P] /\ clock<=asset_contract["CAROL"].deadline /\asset_contract["CAROL"].state =INIT
               THEN /\ asset_contract' = [asset_contract EXCEPT !["CAROL"].state = ESCROW,
                                                                !["CAROL"].timestamp = clock,
                                                                !["CAROL"].timeout = hashkey["C2A"].deadline]
                    /\ step_taken' = [step_taken EXCEPT ![C_E] = TRUE]
                    /\ UNCHANGED premium_contract
               ELSE /\ IF premium_contract["ALICE"].state=ESCROW
                          THEN /\ premium_contract' = [premium_contract EXCEPT !["ALICE"].state = REFUNDED]
                          ELSE /\ TRUE
                               /\ UNCHANGED premium_contract
                    /\ UNCHANGED << asset_contract, step_taken >>
         /\ IF ~step_considered[B_E]/\ clock<=asset_contract'["BOB"].deadline
               THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
               ELSE /\ IF ~step_taken'[B_E]/\step_taken'[C_E]
                          THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
                          ELSE /\ IF step_taken'[B_E]/\step_taken'[A_D_P]/\~step_taken'[C_E]
                                     THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED conforming
         /\ step_considered' = [step_considered EXCEPT ![C_E] = TRUE]
         /\ pc' = [pc EXCEPT ![ETHER] = "S_A_R"]
         /\ UNCHANGED << wallet, hashkey, clock >>

S_A_R == /\ pc[ETHER] = "S_A_R"
         /\ IF step_taken[C_E]/\clock<=asset_contract["CAROL"].timeout/\asset_contract["CAROL"].state = ESCROW
               THEN /\ asset_contract' = [asset_contract EXCEPT !["CAROL"].state = REDEEMED]
                    /\ IF premium_contract["ALICE"].state = ESCROW
                          THEN /\ premium_contract' = [premium_contract EXCEPT !["ALICE"].state = REFUNDED]
                          ELSE /\ TRUE
                               /\ UNCHANGED premium_contract
                    /\ wallet' = [wallet EXCEPT !["CAROL"].balance = wallet["CAROL"].balance-asset_contract'["CAROL"].balance,
                                                !["ALICE"].balance = wallet["ALICE"].balance+asset_contract'["CAROL"].balance]
                    /\ step_taken' = [step_taken EXCEPT ![A_R] = TRUE]
               ELSE /\ IF step_taken[C_E] /\asset_contract["CAROL"].state = ESCROW
                          THEN /\ asset_contract' = [asset_contract EXCEPT !["CAROL"].state = REFUNDED]
                               /\ IF premium_contract["ALICE"].state = ESCROW
                                     THEN /\ premium_contract' = [premium_contract EXCEPT !["ALICE"].state = LOST]
                                          /\ wallet' = [wallet EXCEPT !["CAROL"].balance = wallet["CAROL"].balance+premium_contract'["ALICE"].balance,
                                                                      !["ALICE"].balance = wallet["ALICE"].balance-premium_contract'["ALICE"].balance]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << premium_contract, 
                                                          wallet >>
                          ELSE /\ TRUE
                               /\ UNCHANGED << asset_contract, 
                                               premium_contract, wallet >>
                    /\ UNCHANGED step_taken
         /\ IF ~step_considered[C_E]/\ clock<=asset_contract'["CAROL"].deadline
               THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
               ELSE /\ IF step_taken'[C_E]/\~step_taken'[A_R]
                          THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                          ELSE /\ IF ~step_taken'[C_E]/\step_taken'[A_R]
                                     THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED conforming
         /\ step_considered' = [step_considered EXCEPT ![A_R] = TRUE]
         /\ pc' = [pc EXCEPT ![ETHER] = "Done"]
         /\ UNCHANGED << hashkey, clock >>

ether == S_A_D_P \/ S_C_E \/ S_A_R

tick == /\ pc[CLOCK] = "tick"
        /\ IF (clock <LIMIT)
              THEN /\ pc' = [pc EXCEPT ![CLOCK] = "tok"]
              ELSE /\ pc' = [pc EXCEPT ![CLOCK] = "Done"]
        /\ UNCHANGED << asset_contract, premium_contract, wallet, hashkey, 
                        clock, step_considered, conforming, step_taken >>

tok == /\ pc[CLOCK] = "tok"
       /\ clock' = clock + 1
       /\ pc' = [pc EXCEPT ![CLOCK] = "tick"]
       /\ UNCHANGED << asset_contract, premium_contract, wallet, hashkey, 
                       step_considered, conforming, step_taken >>

Clock == tick \/ tok

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == bitcoin \/ litecoin \/ ether \/ Clock
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(bitcoin)
        /\ WF_vars(litecoin)
        /\ WF_vars(ether)
        /\ WF_vars(Clock)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ecb724fa97049034828931bcaeb2fece
====
