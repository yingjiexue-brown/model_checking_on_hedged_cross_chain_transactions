 ------------------------- MODULE three_party_swap_with_premium -------------------------

EXTENDS Integers, TLC
(* --algorithm example

variables
(*
Protocol description:
Three-party-swap: Goal: Alice(leader) pays 100$ BTC to Bob, 
                   Bob pays 100$ LTC to carol, 
                   Carol  pays $100 ether to Alice (the above does not show the order of those actions )
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

The challenge here is to define if a party is conforming or not:

Principle 1: up to a party takes its step, say step 4, 
            if all previous steps (0-3) are taken in the right order in the protocol and later steps are not taken(5-8),
            then:
            if this party takes step 4 according to the protocol, this party is conforming;
            if this party skip, he/she is not-conforming
            
Principle 2: If the protocol is already messed up, those steps must be considered to be taken/skipped in the right order 
            according to the protocol. If a step is considered in advance, this party is non-conforming.
            

principle 3:   If the protocol is already messed up,i.e. the protocol is already broken, 
              we decide a party is conforming or not out of its own interest, to maximize its utility; 
              most of the time, if the previous step is taken,say step 4, they should take step 5 even though the protocol is broken
              

*)
    \* A swap swap_contract has balance, timeout is initialized as -1 and it will be changed after it is escrowed;
    \* a deadline to be escrowed
    swap_contract = [ALICE |-> [balance |->100, timeout |-> -1, state |-> INIT,deadline |-> 3, timestamp |-> LIMIT],
                BOB|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 4, timestamp |-> LIMIT],
                CAROL|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 5, timestamp |-> LIMIT]],
    \* A premium swap_contract has balance, timeout is initialized as -1 and it will be changed after it is escrowed; 
    \* a deadline to escrow it
    premium = [ALICE |-> [balance|->3, timeout |-> -1, state |-> INIT,deadline |-> 0, timestamp |-> LIMIT],
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
 INIT == 0 ESCROW == 1 REDEEMED == 2 REFUNDED == 3 LOST ==4 EXPIRED == 5 \* swap_contract states
 ALICE == 0 BOB == 1 CAROL ==2  \* ID for parties
 BITCOIN == 0 LITECOIN ==1 ETHER ==2 CLOCK == 3    \* process ids
 LIMIT == 9                         \* max clock value
 PARTIES == {ALICE, BOB, CAROL}            \* parties
 A_D_P == 0  C_D_P == 1 B_D_P ==2 A_E==3 B_E==4 C_E==5
 A_R==6 C_R==7 B_R==8
 
 STEPS == {A_D_P, B_D_P,C_D_P,A_E,B_E,C_E, A_R,B_R,C_R} 
 
 ending == /\ step_considered[A_R]/\step_considered[B_R]/\step_considered[C_R]
 liveness == /\ending/\premium["ALICE"].state=REFUNDED /\premium["BOB"].state=REFUNDED/\premium["CAROL"].state=REFUNDED/\swap_contract["ALICE"].state=REDEEMED /\swap_contract["BOB"].state=REDEEMED/\swap_contract["CAROL"].state=REDEEMED/\conforming[ALICE]/\conforming[BOB]/\conforming[CAROL]
 compensated_alice == (/\ending/\conforming[ALICE]/\swap_contract["ALICE"].state=REFUNDED) => wallet["ALICE"].balance>=wallet["ALICE"].init+1
 compensated_bob == (/\ending/\conforming[BOB]/\swap_contract["BOB"].state=REFUNDED) => wallet["BOB"].balance>=wallet["BOB"].init+1
 safe_alice == (/\ending/\conforming[ALICE]) => wallet["ALICE"].balance>=wallet["ALICE"].init
 safe_bob == (/\ending/\conforming[BOB]) => wallet["BOB"].balance>=wallet["BOB"].init
 compensated_carol == (/\ending/\conforming[CAROL]/\swap_contract["CAROL"].state=REFUNDED) => wallet["CAROL"].balance>=wallet["CAROL"].init+1
 safe_carol == (/\ending/\conforming[CAROL]) => wallet["CAROL"].balance>=wallet["CAROL"].init
 
 
end define;

\* Bitcoin process (A2B) =======================================================================================================
fair process bitcoin = BITCOIN begin 

S_B_D_P: \*clock =2, BOB deposits his premium
    
    if clock<= premium["BOB"].deadline /\ premium["BOB"].state=INIT then \*otherwise, Bob can do nothing
       premium["BOB"].state:=ESCROW 
              || premium["BOB"].timestamp:=clock
              ||premium["BOB"].timeout:=swap_contract["ALICE"].deadline;
              step_taken[B_D_P]:= TRUE;
    else
       skip;
    end if;
    
    if ~step_considered[C_D_P] /\ clock<=premium["CAROL"].deadline then
       conforming[BOB]:=FALSE;
     elsif ~step_taken[C_D_P]/\step_taken[B_D_P] then \* if alice does not deposit premiums, carol deposits hers, carol is crazy
       conforming[BOB]:=FALSE;
     elsif step_taken[C_D_P]/\~step_taken[B_D_P] then \* if alice  deposits premiums, carol does not deposit hers, carol is non-conforming                                        \* Todo: what if bob deposits his premium ealier?
        conforming[BOB]:=FALSE;
    end if;
    step_considered[B_D_P]:=TRUE;

    

S_A_E:\*clock =3, Alice publishes her  swap_contract

    if step_taken[B_D_P] /\ clock <= swap_contract["ALICE"].deadline /\  swap_contract["ALICE"].state = INIT then \*if DP2 finishes, Alice can choose to escrow her swap swap_contract or not
           swap_contract["ALICE"].state := ESCROW
           ||swap_contract["ALICE"].timestamp := clock
           ||swap_contract["ALICE"].timeout := hashkey["A2B"].deadline; 
           step_taken[A_E]:= TRUE;
       
    elsif  premium["BOB"].state=ESCROW then
           premium["BOB"].state:=REFUNDED 
    end if;
    
     if ~step_considered[B_D_P] /\ clock<=premium["BOB"].deadline then
        conforming[ALICE]:=FALSE;
    elsif ~step_taken[B_D_P]/\step_taken[A_E]then 
     conforming[ALICE]:=FALSE;
    elsif step_taken[B_D_P]/\~step_taken[A_E] then 
     conforming[ALICE]:=FALSE;
    end if;
    step_considered[A_E]:=TRUE;
   

S_B_R:\* clock =8,Bob redeems
    if  step_taken[A_E]/\step_taken[C_R]/\clock<=swap_contract["ALICE"].timeout/\ swap_contract["ALICE"].state= ESCROW then
        swap_contract["ALICE"].state:= REDEEMED;
        premium["BOB"].state:=REFUNDED;
        wallet["BOB"].balance:=wallet["BOB"].balance+swap_contract["ALICE"].balance
        ||wallet["ALICE"].balance:=wallet["ALICE"].balance-swap_contract["ALICE"].balance;
        step_taken[B_R]:= TRUE;
        
    elsif step_taken[A_E]/\ swap_contract["ALICE"].state= ESCROW then
         swap_contract["ALICE"].state := REFUNDED;
         premium["BOB"].state:=LOST;
         wallet["BOB"].balance := wallet["BOB"].balance-premium["BOB"].balance
         ||wallet["ALICE"].balance := wallet["ALICE"].balance+premium["BOB"].balance;
    end if;
  
    if ~step_considered[C_R]/\clock<= hashkey["B2C"].deadline then
       conforming[BOB]:=FALSE;
    elsif step_taken[C_R]/\step_taken[A_E]/\~step_taken[B_R] then
        conforming[BOB]:=FALSE;
    end if;
  
    step_considered[B_R]:=TRUE;
end process

\* Litecoin process (B2C)=======================================================================================================
fair process litecoin=LITECOIN begin

S_C_D_P:\*clock =1, carol deposits her premium
    if clock<=premium["CAROL"].deadline /\ premium["CAROL"].state=INIT then 
         premium["CAROL"].timestamp:=clock 
               || premium["CAROL"].state:=ESCROW
               ||premium["CAROL"].timeout:=swap_contract["BOB"].deadline;
               step_taken[C_D_P]:= TRUE;
    else
        skip;
    end if;
    
     if ~step_considered[A_D_P] /\ clock<=premium["ALICE"].deadline then
       conforming[CAROL]:=FALSE;
     elsif ~step_taken[A_D_P]/\step_taken[C_D_P] then \* if alice does not deposit premiums, carol deposits hers, carol is crazy
       conforming[CAROL]:=FALSE;
     elsif step_taken[A_D_P]/\~step_taken[C_D_P] then \* if alice  deposits premiums, carol does not deposit hers, carol is non-conforming                                        \* Todo: what if bob deposits his premium ealier?
       conforming[CAROL]:=FALSE;
    end if;
    step_considered[C_D_P]:=TRUE;
  

S_B_E:\*clock =4, Bob publishes his  swap_contract
    if step_taken[C_D_P] /\ clock<=swap_contract["BOB"].deadline /\ swap_contract["BOB"].state = INIT then
                 swap_contract["BOB"].state := ESCROW
                ||swap_contract["BOB"].timestamp := clock
                ||swap_contract["BOB"].timeout:=hashkey["B2C"].deadline; 
                step_taken[B_E]:=TRUE;
       
    elsif premium["CAROL"].state=ESCROW then
          premium["CAROL"].state:=REFUNDED;
    end if;
    
    if ~step_considered[A_E] /\ clock<=swap_contract["ALICE"].deadline then
       conforming[BOB]:=FALSE;
    elsif step_taken[A_E]/\step_taken[C_D_P]/\~step_taken[B_E]then
       conforming[BOB]:=FALSE;
    elsif ~step_taken[A_E]/\step_taken[B_E]then
     conforming[BOB]:=FALSE;
    end if;
    
    step_considered[B_E]:=TRUE;
    
  
    
    
S_C_R:\*clock =7, carol redeems
    if step_taken[B_E]/\step_taken[A_R]/\clock<=swap_contract["BOB"].timeout /\ swap_contract["BOB"].state = ESCROW then
               swap_contract["BOB"].state := REDEEMED;
               premium["CAROL"].state:=REFUNDED;
               wallet["BOB"].balance := wallet["BOB"].balance-swap_contract["BOB"].balance
               ||wallet["CAROL"].balance := wallet["CAROL"].balance+swap_contract["BOB"].balance;
               step_taken[C_R]:=TRUE;
      
    elsif step_taken[B_E] /\ swap_contract["BOB"].state = ESCROW then 
           swap_contract["BOB"].state := REFUNDED;
           premium["CAROL"].state:=LOST;
           wallet["BOB"].balance := wallet["BOB"].balance+premium["CAROL"].balance
           ||wallet["CAROL"].balance := wallet["CAROL"].balance-premium["CAROL"].balance
    end if;
    if ~step_considered[A_R] /\ clock<= hashkey["C2A"].deadline then
       conforming[CAROL]:=FALSE;
    elsif step_taken[A_R]/\step_taken[B_E]/\~step_taken[C_R]then
        conforming[CAROL]:=FALSE;
    end if;
    step_considered[C_R]:=TRUE;
end process

\* Ether process: C2A =======================================================================================================

fair process ether=ETHER begin

S_A_D_P:\* clock =0 ,Alice deposits her premium in Ether
    if clock<=premium["ALICE"].deadline /\ premium["ALICE"].state=INIT then \*otherwise, Alice cannot escrow
               premium["ALICE"].timestamp:=clock 
               || premium["ALICE"].state:=ESCROW
               ||premium["ALICE"].timeout:=swap_contract["CAROL"].deadline; 
               step_taken[A_D_P]:= TRUE;
    else
        skip;
    end if;
    
    if ~step_taken[A_D_P] then
       conforming[ALICE]:=FALSE;
    end if;
    
    step_considered[A_D_P]:=TRUE;
 

S_C_E:\*clock =5, Carol publishes her swap_contract
    if step_taken[A_D_P] /\ clock<=swap_contract["CAROL"].deadline /\swap_contract["CAROL"].state =INIT then
                 swap_contract["CAROL"].state := ESCROW
                ||swap_contract["CAROL"].timestamp := clock
                ||swap_contract["CAROL"].timeout:=hashkey["C2A"].deadline;
                step_taken[C_E]:=TRUE;
        
    elsif premium["ALICE"].state=ESCROW then
          premium["ALICE"].state:=REFUNDED;
       
    end if;
   
    if ~step_considered[B_E]/\ clock<=swap_contract["BOB"].deadline then 
    conforming[CAROL]:=FALSE;
    elsif ~step_taken[B_E]/\step_taken[C_E]then
     conforming[CAROL]:=FALSE;
    elsif step_taken[B_E]/\step_taken[A_D_P]/\~step_taken[C_E]then
     conforming[CAROL]:=FALSE;
    end if;
    
    step_considered[C_E]:=TRUE;
 

S_A_R:\*clock =6, Alice redeems
    
    if step_taken[C_E]/\clock<=swap_contract["CAROL"].timeout/\swap_contract["CAROL"].state = ESCROW then
                swap_contract["CAROL"].state := REDEEMED;
               premium["ALICE"].state:=REFUNDED;
               wallet["CAROL"].balance := wallet["CAROL"].balance-swap_contract["CAROL"].balance
               ||wallet["ALICE"].balance := wallet["ALICE"].balance+swap_contract["CAROL"].balance;
               step_taken[A_R]:=TRUE;
       
    elsif step_taken[C_E] /\swap_contract["CAROL"].state = ESCROW then \* Alice is too late
           swap_contract["CAROL"].state := REFUNDED;
           premium["ALICE"].state:=LOST;
           wallet["CAROL"].balance := wallet["CAROL"].balance+premium["ALICE"].balance
           ||wallet["ALICE"].balance := wallet["ALICE"].balance-premium["ALICE"].balance
    end if;
   
   
    if ~step_considered[C_E]/\ clock<=swap_contract["CAROL"].deadline then
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-2dbd5b1cfe62f793b7be07eb23af5089
VARIABLES swap_contract, premium, wallet, hashkey, clock, step_considered, 
          conforming, step_taken, pc

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
liveness == /\ending/\premium["ALICE"].state=REFUNDED /\premium["BOB"].state=REFUNDED/\premium["CAROL"].state=REFUNDED/\swap_contract["ALICE"].state=REDEEMED /\swap_contract["BOB"].state=REDEEMED/\swap_contract["CAROL"].state=REDEEMED/\conforming[ALICE]/\conforming[BOB]/\conforming[CAROL]
compensated_alice == (/\ending/\conforming[ALICE]/\swap_contract["ALICE"].state=REFUNDED) => wallet["ALICE"].balance>=wallet["ALICE"].init+1
compensated_bob == (/\ending/\conforming[BOB]/\swap_contract["BOB"].state=REFUNDED) => wallet["BOB"].balance>=wallet["BOB"].init+1
safe_alice == (/\ending/\conforming[ALICE]) => wallet["ALICE"].balance>=wallet["ALICE"].init
safe_bob == (/\ending/\conforming[BOB]) => wallet["BOB"].balance>=wallet["BOB"].init
compensated_carol == (/\ending/\conforming[CAROL]/\swap_contract["CAROL"].state=REFUNDED) => wallet["CAROL"].balance>=wallet["CAROL"].init+1
safe_carol == (/\ending/\conforming[CAROL]) => wallet["CAROL"].balance>=wallet["CAROL"].init


vars == << swap_contract, premium, wallet, hashkey, clock, step_considered, 
           conforming, step_taken, pc >>

ProcSet == {BITCOIN} \cup {LITECOIN} \cup {ETHER} \cup {CLOCK}

Init == (* Global variables *)
        /\ swap_contract =     [ALICE |-> [balance |->100, timeout |-> -1, state |-> INIT,deadline |-> 3, timestamp |-> LIMIT],
                           BOB|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 4, timestamp |-> LIMIT],
                           CAROL|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 5, timestamp |-> LIMIT]]
        /\ premium = [ALICE |-> [balance|->3, timeout |-> -1, state |-> INIT,deadline |-> 0, timestamp |-> LIMIT],
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
           /\ IF clock<= premium["BOB"].deadline /\ premium["BOB"].state=INIT
                 THEN /\ premium' = [premium EXCEPT !["BOB"].state = ESCROW,
                                                    !["BOB"].timestamp = clock,
                                                    !["BOB"].timeout = swap_contract["ALICE"].deadline]
                      /\ step_taken' = [step_taken EXCEPT ![B_D_P] = TRUE]
                 ELSE /\ TRUE
                      /\ UNCHANGED << premium, step_taken >>
           /\ IF ~step_considered[C_D_P] /\ clock<=premium'["CAROL"].deadline
                 THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                 ELSE /\ IF ~step_taken'[C_D_P]/\step_taken'[B_D_P]
                            THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                            ELSE /\ IF step_taken'[C_D_P]/\~step_taken'[B_D_P]
                                       THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED conforming
           /\ step_considered' = [step_considered EXCEPT ![B_D_P] = TRUE]
           /\ pc' = [pc EXCEPT ![BITCOIN] = "S_A_E"]
           /\ UNCHANGED << swap_contract, wallet, hashkey, clock >>

S_A_E == /\ pc[BITCOIN] = "S_A_E"
         /\ IF step_taken[B_D_P] /\ clock <= swap_contract["ALICE"].deadline /\  swap_contract["ALICE"].state = INIT
               THEN /\ swap_contract' = [swap_contract EXCEPT !["ALICE"].state = ESCROW,
                                                              !["ALICE"].timestamp = clock,
                                                              !["ALICE"].timeout = hashkey["A2B"].deadline]
                    /\ step_taken' = [step_taken EXCEPT ![A_E] = TRUE]
                    /\ UNCHANGED premium
               ELSE /\ IF premium["BOB"].state=ESCROW
                          THEN /\ premium' = [premium EXCEPT !["BOB"].state = REFUNDED]
                          ELSE /\ TRUE
                               /\ UNCHANGED premium
                    /\ UNCHANGED << swap_contract, step_taken >>
         /\ IF ~step_considered[B_D_P] /\ clock<=premium'["BOB"].deadline
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
         /\ IF step_taken[A_E]/\step_taken[C_R]/\clock<=swap_contract["ALICE"].timeout/\ swap_contract["ALICE"].state= ESCROW
               THEN /\ swap_contract' = [swap_contract EXCEPT !["ALICE"].state = REDEEMED]
                    /\ premium' = [premium EXCEPT !["BOB"].state = REFUNDED]
                    /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance+swap_contract'["ALICE"].balance,
                                                !["ALICE"].balance = wallet["ALICE"].balance-swap_contract'["ALICE"].balance]
                    /\ step_taken' = [step_taken EXCEPT ![B_R] = TRUE]
               ELSE /\ IF step_taken[A_E]/\ swap_contract["ALICE"].state= ESCROW
                          THEN /\ swap_contract' = [swap_contract EXCEPT !["ALICE"].state = REFUNDED]
                               /\ premium' = [premium EXCEPT !["BOB"].state = LOST]
                               /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance-premium'["BOB"].balance,
                                                           !["ALICE"].balance = wallet["ALICE"].balance+premium'["BOB"].balance]
                          ELSE /\ TRUE
                               /\ UNCHANGED << swap_contract, premium, wallet >>
                    /\ UNCHANGED step_taken
         /\ IF ~step_considered[C_R]/\clock<= hashkey["B2C"].deadline
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
           /\ IF clock<=premium["CAROL"].deadline /\ premium["CAROL"].state=INIT
                 THEN /\ premium' = [premium EXCEPT !["CAROL"].timestamp = clock,
                                                    !["CAROL"].state = ESCROW,
                                                    !["CAROL"].timeout = swap_contract["BOB"].deadline]
                      /\ step_taken' = [step_taken EXCEPT ![C_D_P] = TRUE]
                 ELSE /\ TRUE
                      /\ UNCHANGED << premium, step_taken >>
           /\ IF ~step_considered[A_D_P] /\ clock<=premium'["ALICE"].deadline
                 THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
                 ELSE /\ IF ~step_taken'[A_D_P]/\step_taken'[C_D_P]
                            THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
                            ELSE /\ IF step_taken'[A_D_P]/\~step_taken'[C_D_P]
                                       THEN /\ conforming' = [conforming EXCEPT ![CAROL] = FALSE]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED conforming
           /\ step_considered' = [step_considered EXCEPT ![C_D_P] = TRUE]
           /\ pc' = [pc EXCEPT ![LITECOIN] = "S_B_E"]
           /\ UNCHANGED << swap_contract, wallet, hashkey, clock >>

S_B_E == /\ pc[LITECOIN] = "S_B_E"
         /\ IF step_taken[C_D_P] /\ clock<=swap_contract["BOB"].deadline /\ swap_contract["BOB"].state = INIT
               THEN /\ swap_contract' = [swap_contract EXCEPT !["BOB"].state = ESCROW,
                                                              !["BOB"].timestamp = clock,
                                                              !["BOB"].timeout = hashkey["B2C"].deadline]
                    /\ step_taken' = [step_taken EXCEPT ![B_E] = TRUE]
                    /\ UNCHANGED premium
               ELSE /\ IF premium["CAROL"].state=ESCROW
                          THEN /\ premium' = [premium EXCEPT !["CAROL"].state = REFUNDED]
                          ELSE /\ TRUE
                               /\ UNCHANGED premium
                    /\ UNCHANGED << swap_contract, step_taken >>
         /\ IF ~step_considered[A_E] /\ clock<=swap_contract'["ALICE"].deadline
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
         /\ IF step_taken[B_E]/\step_taken[A_R]/\clock<=swap_contract["BOB"].timeout /\ swap_contract["BOB"].state = ESCROW
               THEN /\ swap_contract' = [swap_contract EXCEPT !["BOB"].state = REDEEMED]
                    /\ premium' = [premium EXCEPT !["CAROL"].state = REFUNDED]
                    /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance-swap_contract'["BOB"].balance,
                                                !["CAROL"].balance = wallet["CAROL"].balance+swap_contract'["BOB"].balance]
                    /\ step_taken' = [step_taken EXCEPT ![C_R] = TRUE]
               ELSE /\ IF step_taken[B_E] /\ swap_contract["BOB"].state = ESCROW
                          THEN /\ swap_contract' = [swap_contract EXCEPT !["BOB"].state = REFUNDED]
                               /\ premium' = [premium EXCEPT !["CAROL"].state = LOST]
                               /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance+premium'["CAROL"].balance,
                                                           !["CAROL"].balance = wallet["CAROL"].balance-premium'["CAROL"].balance]
                          ELSE /\ TRUE
                               /\ UNCHANGED << swap_contract, premium, wallet >>
                    /\ UNCHANGED step_taken
         /\ IF ~step_considered[A_R] /\ clock<= hashkey["C2A"].deadline
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
           /\ IF clock<=premium["ALICE"].deadline /\ premium["ALICE"].state=INIT
                 THEN /\ premium' = [premium EXCEPT !["ALICE"].timestamp = clock,
                                                    !["ALICE"].state = ESCROW,
                                                    !["ALICE"].timeout = swap_contract["CAROL"].deadline]
                      /\ step_taken' = [step_taken EXCEPT ![A_D_P] = TRUE]
                 ELSE /\ TRUE
                      /\ UNCHANGED << premium, step_taken >>
           /\ IF ~step_taken'[A_D_P]
                 THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                 ELSE /\ TRUE
                      /\ UNCHANGED conforming
           /\ step_considered' = [step_considered EXCEPT ![A_D_P] = TRUE]
           /\ pc' = [pc EXCEPT ![ETHER] = "S_C_E"]
           /\ UNCHANGED << swap_contract, wallet, hashkey, clock >>

S_C_E == /\ pc[ETHER] = "S_C_E"
         /\ IF step_taken[A_D_P] /\ clock<=swap_contract["CAROL"].deadline /\swap_contract["CAROL"].state =INIT
               THEN /\ swap_contract' = [swap_contract EXCEPT !["CAROL"].state = ESCROW,
                                                              !["CAROL"].timestamp = clock,
                                                              !["CAROL"].timeout = hashkey["C2A"].deadline]
                    /\ step_taken' = [step_taken EXCEPT ![C_E] = TRUE]
                    /\ UNCHANGED premium
               ELSE /\ IF premium["ALICE"].state=ESCROW
                          THEN /\ premium' = [premium EXCEPT !["ALICE"].state = REFUNDED]
                          ELSE /\ TRUE
                               /\ UNCHANGED premium
                    /\ UNCHANGED << swap_contract, step_taken >>
         /\ IF ~step_considered[B_E]/\ clock<=swap_contract'["BOB"].deadline
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
         /\ IF step_taken[C_E]/\clock<=swap_contract["CAROL"].timeout/\swap_contract["CAROL"].state = ESCROW
               THEN /\ swap_contract' = [swap_contract EXCEPT !["CAROL"].state = REDEEMED]
                    /\ premium' = [premium EXCEPT !["ALICE"].state = REFUNDED]
                    /\ wallet' = [wallet EXCEPT !["CAROL"].balance = wallet["CAROL"].balance-swap_contract'["CAROL"].balance,
                                                !["ALICE"].balance = wallet["ALICE"].balance+swap_contract'["CAROL"].balance]
                    /\ step_taken' = [step_taken EXCEPT ![A_R] = TRUE]
               ELSE /\ IF step_taken[C_E] /\swap_contract["CAROL"].state = ESCROW
                          THEN /\ swap_contract' = [swap_contract EXCEPT !["CAROL"].state = REFUNDED]
                               /\ premium' = [premium EXCEPT !["ALICE"].state = LOST]
                               /\ wallet' = [wallet EXCEPT !["CAROL"].balance = wallet["CAROL"].balance+premium'["ALICE"].balance,
                                                           !["ALICE"].balance = wallet["ALICE"].balance-premium'["ALICE"].balance]
                          ELSE /\ TRUE
                               /\ UNCHANGED << swap_contract, premium, wallet >>
                    /\ UNCHANGED step_taken
         /\ IF ~step_considered[C_E]/\ clock<=swap_contract'["CAROL"].deadline
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
        /\ UNCHANGED << swap_contract, premium, wallet, hashkey, clock, 
                        step_considered, conforming, step_taken >>

tok == /\ pc[CLOCK] = "tok"
       /\ clock' = clock + 1
       /\ pc' = [pc EXCEPT ![CLOCK] = "tick"]
       /\ UNCHANGED << swap_contract, premium, wallet, hashkey, 
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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5d19c77c845535ce5556f6ecbc72e2b6
====
