------------------------- MODULE two_party_swap_with_premium -------------------------

EXTENDS Integers, TLC
(* --algorithm example

\* Assuming there are two separate swap_contracts on each blockchain describing sequentialized designitated actions on that blockchain 
\* Then, on each blockchain, the party should behave as that swap_contract specifies,
\* otherwise, they are regarded as silent since the swap_contract only allow expected "input" which are swap_contract escrow, swap_contract redeem, etc.
(*protocol description: goal: Alice pays $100 BTC to Bob, Bob pays $100 LTC to alice in exchange;
 steps: (deposit premiums phase ) 
 clock <= 0: Alice deposits $2 LTC; (LTC Blockchain, DP1)
 clock <=1: Bob deposits $1 BTC; (BTC Blockchain, DP2)
 (escrow phase)
 clock <=2: Alice escrows $100 BTC; (BTC Blockchain, AS1)
 clock <=3: Bob escrows $100 LTC; (LTC Blockchain, AS2)
 (redeem phase)
 clock <=4: Alice redeems (LTC Blockchain, AS3)
 clock <=5: Bob redeems (BTC Blockchain, AS4)
 
*)
variables
    \* A swap_contract has balance, timeout is initialized as -1 and will be changed after it is escrowed
    \* a deadline to be escrowed
    \* a timestamp recording when it is escrowed, initialized as LIMIT
    
    swap_contract = [ALICE |-> [balance |->100, timeout |-> -1, state |-> INIT,deadline |-> 2, timestamp |-> LIMIT],
                BOB|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 3, timestamp |-> LIMIT]],
    
    \* A premium swap_contract has balance, timeout is initialized as -1 and will be changed after it is escrowed;
    \* a deadline to be escrowed, a timestamp recording when it is escrowed, initialized as LIMIT
    premium = [ALICE |-> [balance|->2, timeout |-> -1, state |-> INIT,deadline |-> 0, timestamp |-> LIMIT],
               BOB|->[balance|->1, timeout |->-1, state |-> INIT,deadline |-> 1, timestamp |-> LIMIT]],
    hashkey = [B2A|-> [deadline|->4,state|->INIT],A2B|->[deadline|->5,state|->INIT]],
    \* wallet contains amount of assets in this protocol
    wallet = [ALICE |-> [balance|->102,init|->102], BOB|-> [balance|->101,init|->101]],
    \* global clock
    clock = 0,
    \* step only indicates if one single step is done or not
    step_taken = [s \in STEPS |->FALSE],
    \* step_considered indicates if one step is considered, no matter this step is taken according to the swap_contract or skipped
    step_considered = [s \in STEPS |->FALSE],
    conforming = [p \in  PARTIES |->TRUE],
define
 INIT == 0 ESCROW == 1 REDEEMED == 2 REFUNDED == 3 LOST ==4 RELEASED == 5 \* swap_contract states
 ALICE == 0 BOB == 1  \* ID for parties
 BITCOIN == 0 LITECOIN ==1 CLOCK == 2     \* process ids
 LIMIT == 6                         \* max clock value
 PARTIES == {ALICE, BOB}            \* parties
 SDP1 == 0  SDP2 == 1 SAS1 ==2 SAS2==3 SAS3==4 SAS4==5
 STEPS == {SDP1, SDP2,SAS1,SAS2,SAS3,SAS4} 
 ending == /\step_considered[SAS4]/\step_considered[SAS3]
 
 liveness == /\ending/\premium["ALICE"].state=REFUNDED /\premium["BOB"].state=REFUNDED/\swap_contract["ALICE"].state=REDEEMED /\swap_contract["BOB"].state=REDEEMED/\conforming[ALICE]/\conforming[BOB]
 compensated_alice == (/\ending/\conforming[ALICE]/\swap_contract["ALICE"].state=REFUNDED) => wallet["ALICE"].balance>=wallet["ALICE"].init+1
 compensated_bob == (/\ending/\conforming[BOB]/\swap_contract["BOB"].state=REFUNDED) => wallet["BOB"].balance>=wallet["BOB"].init+1
 safe_alice == (/\ending/\conforming[ALICE]) => wallet["ALICE"].balance>=wallet["ALICE"].init
 safe_bob == (/\ending/\conforming[BOB]) => wallet["BOB"].balance>=wallet["BOB"].init
 
end define;
\*=================bitcoin process========================================
fair process bitcoin = BITCOIN begin 

    DP2: \*clock <=1, BOB deposits his premium
    
    if clock<= premium["BOB"].deadline /\ premium["BOB"].state=INIT then \*otherwise, Bob cannot do anything
               premium["BOB"].state:=ESCROW 
              || premium["BOB"].timestamp:=clock
              ||premium["BOB"].timeout:=swap_contract["ALICE"].deadline;
              step_taken[SDP2]:= TRUE;
    else
       skip;
    end if;
    
    \* this part determines if a party is conforming
    if   ~step_considered[SDP1]/\ clock<= premium["ALICE"].deadline then \* 
         conforming[BOB]:=FALSE;
    elsif step_taken[SDP1]/\~step_taken[SDP2] then
          conforming[BOB]:=FALSE;
    elsif ~step_taken[SDP1]/\step_taken[SDP2] then
         conforming[BOB]:=FALSE; 
    end if;
    
    step_considered[SDP2]:=TRUE;
    

    AS1:\*clock <=2, Alice publishes her swap_contract

    if step_taken[SDP2] /\ clock <= swap_contract["ALICE"].deadline /\ swap_contract["ALICE"].state = INIT then \*if DP2 finishes, Alice can choose to escrow her swap swap_contract or not to escrow
           swap_contract["ALICE"].state := ESCROW
           ||swap_contract["ALICE"].timestamp := clock
           ||swap_contract["ALICE"].timeout := hashkey["A2B"].deadline;
           step_taken[SAS1]:= TRUE;
     
    elsif  premium["BOB"].state=ESCROW then
           premium["BOB"].state:=REFUNDED;
    end if;
    
  
  
    if ~step_considered[SDP2]/\ clock<= premium["BOB"].deadline then
         conforming[ALICE]:=FALSE;
    elsif step_taken[SDP2]/\~step_taken[SAS1] then
         conforming[ALICE]:=FALSE;
    elsif ~step_taken[SDP2]/\step_taken[SAS1] then
         conforming[ALICE]:=FALSE;
    end if;
    
    step_considered[SAS1]:=TRUE;
    
    

    AS4:\*clock<=5, Bob redeems
    if  step_taken[SAS1]/\step_taken[SAS3]/\clock<=swap_contract["ALICE"].timeout/\ swap_contract["ALICE"].state= ESCROW then \* note that we do not require as3 to finish to finish as4
        swap_contract["ALICE"].state:= REDEEMED;
        premium["BOB"].state:=REFUNDED;
        wallet["BOB"].balance:=wallet["BOB"].balance +swap_contract["ALICE"].balance
        ||wallet["ALICE"].balance:=wallet["ALICE"].balance-swap_contract["ALICE"].balance;
        step_taken[SAS4]:= TRUE;
       
    elsif step_taken[SAS1]/\ swap_contract["ALICE"].state= ESCROW then
         swap_contract["ALICE"].state := REFUNDED;
         premium["BOB"].state:=LOST;
         wallet["BOB"].balance := wallet["BOB"].balance-premium["BOB"].balance
         ||wallet["ALICE"].balance := wallet["ALICE"].balance+premium["BOB"].balance;
    end if;
    
    \* this part determines the whether they are conforming and the protocol goes well
    if  ~step_considered[SAS3] /\ clock<=hashkey["B2A"].deadline then
       conforming[BOB]:= FALSE; 
    elsif step_taken[SAS3]/\step_taken[SAS1]/\~step_taken[SAS4] then
       conforming[BOB]:= FALSE; 
    end if;
    
    step_considered[SAS4]:=TRUE;
end process
\*=================litcoin process========================================
fair process litecoin=LITECOIN begin

    DP1:\* clock=0, Alice deposits her premium
    if clock<=premium["ALICE"].deadline /\ premium["ALICE"].state=INIT then \* otherwise, LTC does not accept escrow, i.e. alice is silent
               premium["ALICE"].timestamp:=clock 
               || premium["ALICE"].state:=ESCROW
               ||premium["ALICE"].timeout:=swap_contract["BOB"].deadline; \*premium["ALICE"] timeouts if swap_contract["BOB"]is not published before deadline
               step_taken[SDP1]:= TRUE;       
    
    else \* nothing happens
        skip;
    end if;

    \* this part determines if a party is conforming
    if    ~step_taken[SDP1] then
         conforming[ALICE]:= FALSE;
    end if;
    
    step_considered[SDP1]:=TRUE;
    
    

    AS2:\* clock <=3, Bob publishes his swap swap_contract
    if step_taken[SDP1] /\ clock<=swap_contract["BOB"].deadline /\  swap_contract["BOB"].state = INIT then
                swap_contract["BOB"].state := ESCROW
                ||swap_contract["BOB"].timestamp := clock
                ||swap_contract["BOB"].timeout:=hashkey["B2A"].deadline;
                step_taken[SAS2]:=TRUE;
    
    elsif premium["ALICE"].state=ESCROW then
          premium["ALICE"].state:= REFUNDED;
    end if;
    
    \* this part determines if a party is conforming
    if  ~step_considered[SAS1] /\ clock<=swap_contract["ALICE"].deadline then
         conforming[BOB]:=FALSE;
    elsif step_taken[SAS1] /\ step_taken[SDP1]/\~step_taken[SAS2] then
         conforming[BOB]:=FALSE;
    elsif ~step_taken[SAS1] /\ step_taken[SAS2] then
        conforming[BOB]:=FALSE;
    end if;

    step_considered[SAS2]:=TRUE;

    AS3:\*clock<=4, Alice redeems
    
    if step_taken[SAS2]/\clock<=swap_contract["BOB"].timeout/\swap_contract["BOB"].state = ESCROW then
                swap_contract["BOB"].state := REDEEMED;\* first Alice observes the state on the chain; regardless Bob is conforming or not
               premium["ALICE"].state:=REFUNDED;
               wallet["BOB"].balance := wallet["BOB"].balance-swap_contract["BOB"].balance \*Bob loses $100
               ||wallet["ALICE"].balance := wallet["ALICE"].balance + swap_contract["BOB"].balance;\*alice gets $100
               step_taken[SAS3]:=TRUE;
     
    elsif step_taken[SAS2] /\swap_contract["BOB"].state = ESCROW then \* Alice is too late
           swap_contract["BOB"].state := REFUNDED;
           premium["ALICE"].state:=LOST;
           wallet["BOB"].balance := wallet["BOB"].balance+premium["ALICE"].balance
           ||wallet["ALICE"].balance := wallet["ALICE"].balance-premium["ALICE"].balance
    end if;
  
    \* this part determines if a party is conforming and the protocol goes well
    if ~step_considered[SAS2]/\clock<=swap_contract["BOB"].deadline then
        conforming[ALICE]:=FALSE;
    elsif step_taken[SAS2]/\~step_taken[SAS3]then
       conforming[ALICE]:=FALSE;
    elsif ~step_taken[SAS2]/\step_taken[SAS3] then \* if bob escrows but alice does not redeem, alice is crazy
       conforming[ALICE]:=FALSE;
    end if;
    step_considered[SAS3]:=TRUE;
end process

fair process Clock = CLOCK begin tik:
    while (clock <LIMIT) do
    tok: clock := clock + 1;
    end while;
 end process

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-59c3310921b1d214b696e8af65f90741
VARIABLES swap_contract, premium, hashkey, wallet, clock, step_taken, 
          step_considered, conforming, pc

(* define statement *)
INIT == 0 ESCROW == 1 REDEEMED == 2 REFUNDED == 3 LOST ==4 RELEASED == 5
ALICE == 0 BOB == 1
BITCOIN == 0 LITECOIN ==1 CLOCK == 2
LIMIT == 6
PARTIES == {ALICE, BOB}
SDP1 == 0  SDP2 == 1 SAS1 ==2 SAS2==3 SAS3==4 SAS4==5
STEPS == {SDP1, SDP2,SAS1,SAS2,SAS3,SAS4}
ending == /\step_considered[SAS4]/\step_considered[SAS3]

liveness == /\ending/\premium["ALICE"].state=REFUNDED /\premium["BOB"].state=REFUNDED/\swap_contract["ALICE"].state=REDEEMED /\swap_contract["BOB"].state=REDEEMED/\conforming[ALICE]/\conforming[BOB]
compensated_alice == (/\ending/\conforming[ALICE]/\swap_contract["ALICE"].state=REFUNDED) => wallet["ALICE"].balance>=wallet["ALICE"].init+1
compensated_bob == (/\ending/\conforming[BOB]/\swap_contract["BOB"].state=REFUNDED) => wallet["BOB"].balance>=wallet["BOB"].init+1
safe_alice == (/\ending/\conforming[ALICE]) => wallet["ALICE"].balance>=wallet["ALICE"].init
safe_bob == (/\ending/\conforming[BOB]) => wallet["BOB"].balance>=wallet["BOB"].init


vars == << swap_contract, premium, hashkey, wallet, clock, step_taken, 
           step_considered, conforming, pc >>

ProcSet == {BITCOIN} \cup {LITECOIN} \cup {CLOCK}

Init == (* Global variables *)
        /\ swap_contract =     [ALICE |-> [balance |->100, timeout |-> -1, state |-> INIT,deadline |-> 2, timestamp |-> LIMIT],
                           BOB|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 3, timestamp |-> LIMIT]]
        /\ premium = [ALICE |-> [balance|->2, timeout |-> -1, state |-> INIT,deadline |-> 0, timestamp |-> LIMIT],
                      BOB|->[balance|->1, timeout |->-1, state |-> INIT,deadline |-> 1, timestamp |-> LIMIT]]
        /\ hashkey = [B2A|-> [deadline|->4,state|->INIT],A2B|->[deadline|->5,state|->INIT]]
        /\ wallet = [ALICE |-> [balance|->102,init|->102], BOB|-> [balance|->101,init|->101]]
        /\ clock = 0
        /\ step_taken = [s \in STEPS |->FALSE]
        /\ step_considered = [s \in STEPS |->FALSE]
        /\ conforming = [p \in  PARTIES |->TRUE]
        /\ pc = [self \in ProcSet |-> CASE self = BITCOIN -> "DP2"
                                        [] self = LITECOIN -> "DP1"
                                        [] self = CLOCK -> "tik"]

DP2 == /\ pc[BITCOIN] = "DP2"
       /\ IF clock<= premium["BOB"].deadline /\ premium["BOB"].state=INIT
             THEN /\ premium' = [premium EXCEPT !["BOB"].state = ESCROW,
                                                !["BOB"].timestamp = clock,
                                                !["BOB"].timeout = swap_contract["ALICE"].deadline]
                  /\ step_taken' = [step_taken EXCEPT ![SDP2] = TRUE]
             ELSE /\ TRUE
                  /\ UNCHANGED << premium, step_taken >>
       /\ IF ~step_considered[SDP1]/\ clock<= premium'["ALICE"].deadline
             THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
             ELSE /\ IF step_taken'[SDP1]/\~step_taken'[SDP2]
                        THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                        ELSE /\ IF ~step_taken'[SDP1]/\step_taken'[SDP2]
                                   THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED conforming
       /\ step_considered' = [step_considered EXCEPT ![SDP2] = TRUE]
       /\ pc' = [pc EXCEPT ![BITCOIN] = "AS1"]
       /\ UNCHANGED << swap_contract, hashkey, wallet, clock >>

AS1 == /\ pc[BITCOIN] = "AS1"
       /\ IF step_taken[SDP2] /\ clock <= swap_contract["ALICE"].deadline /\ swap_contract["ALICE"].state = INIT
             THEN /\ swap_contract' = [swap_contract EXCEPT !["ALICE"].state = ESCROW,
                                                            !["ALICE"].timestamp = clock,
                                                            !["ALICE"].timeout = hashkey["A2B"].deadline]
                  /\ step_taken' = [step_taken EXCEPT ![SAS1] = TRUE]
                  /\ UNCHANGED premium
             ELSE /\ IF premium["BOB"].state=ESCROW
                        THEN /\ premium' = [premium EXCEPT !["BOB"].state = REFUNDED]
                        ELSE /\ TRUE
                             /\ UNCHANGED premium
                  /\ UNCHANGED << swap_contract, step_taken >>
       /\ IF ~step_considered[SDP2]/\ clock<= premium'["BOB"].deadline
             THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
             ELSE /\ IF step_taken'[SDP2]/\~step_taken'[SAS1]
                        THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                        ELSE /\ IF ~step_taken'[SDP2]/\step_taken'[SAS1]
                                   THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED conforming
       /\ step_considered' = [step_considered EXCEPT ![SAS1] = TRUE]
       /\ pc' = [pc EXCEPT ![BITCOIN] = "AS4"]
       /\ UNCHANGED << hashkey, wallet, clock >>

AS4 == /\ pc[BITCOIN] = "AS4"
       /\ IF step_taken[SAS1]/\step_taken[SAS3]/\clock<=swap_contract["ALICE"].timeout/\ swap_contract["ALICE"].state= ESCROW
             THEN /\ swap_contract' = [swap_contract EXCEPT !["ALICE"].state = REDEEMED]
                  /\ premium' = [premium EXCEPT !["BOB"].state = REFUNDED]
                  /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance +swap_contract'["ALICE"].balance,
                                              !["ALICE"].balance = wallet["ALICE"].balance-swap_contract'["ALICE"].balance]
                  /\ step_taken' = [step_taken EXCEPT ![SAS4] = TRUE]
             ELSE /\ IF step_taken[SAS1]/\ swap_contract["ALICE"].state= ESCROW
                        THEN /\ swap_contract' = [swap_contract EXCEPT !["ALICE"].state = REFUNDED]
                             /\ premium' = [premium EXCEPT !["BOB"].state = LOST]
                             /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance-premium'["BOB"].balance,
                                                         !["ALICE"].balance = wallet["ALICE"].balance+premium'["BOB"].balance]
                        ELSE /\ TRUE
                             /\ UNCHANGED << swap_contract, premium, wallet >>
                  /\ UNCHANGED step_taken
       /\ IF ~step_considered[SAS3] /\ clock<=hashkey["B2A"].deadline
             THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
             ELSE /\ IF step_taken'[SAS3]/\step_taken'[SAS1]/\~step_taken'[SAS4]
                        THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                        ELSE /\ TRUE
                             /\ UNCHANGED conforming
       /\ step_considered' = [step_considered EXCEPT ![SAS4] = TRUE]
       /\ pc' = [pc EXCEPT ![BITCOIN] = "Done"]
       /\ UNCHANGED << hashkey, clock >>

bitcoin == DP2 \/ AS1 \/ AS4

DP1 == /\ pc[LITECOIN] = "DP1"
       /\ IF clock<=premium["ALICE"].deadline /\ premium["ALICE"].state=INIT
             THEN /\ premium' = [premium EXCEPT !["ALICE"].timestamp = clock,
                                                !["ALICE"].state = ESCROW,
                                                !["ALICE"].timeout = swap_contract["BOB"].deadline]
                  /\ step_taken' = [step_taken EXCEPT ![SDP1] = TRUE]
             ELSE /\ TRUE
                  /\ UNCHANGED << premium, step_taken >>
       /\ IF ~step_taken'[SDP1]
             THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
             ELSE /\ TRUE
                  /\ UNCHANGED conforming
       /\ step_considered' = [step_considered EXCEPT ![SDP1] = TRUE]
       /\ pc' = [pc EXCEPT ![LITECOIN] = "AS2"]
       /\ UNCHANGED << swap_contract, hashkey, wallet, clock >>

AS2 == /\ pc[LITECOIN] = "AS2"
       /\ IF step_taken[SDP1] /\ clock<=swap_contract["BOB"].deadline /\  swap_contract["BOB"].state = INIT
             THEN /\ swap_contract' = [swap_contract EXCEPT !["BOB"].state = ESCROW,
                                                            !["BOB"].timestamp = clock,
                                                            !["BOB"].timeout = hashkey["B2A"].deadline]
                  /\ step_taken' = [step_taken EXCEPT ![SAS2] = TRUE]
                  /\ UNCHANGED premium
             ELSE /\ IF premium["ALICE"].state=ESCROW
                        THEN /\ premium' = [premium EXCEPT !["ALICE"].state = REFUNDED]
                        ELSE /\ TRUE
                             /\ UNCHANGED premium
                  /\ UNCHANGED << swap_contract, step_taken >>
       /\ IF ~step_considered[SAS1] /\ clock<=swap_contract'["ALICE"].deadline
             THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
             ELSE /\ IF step_taken'[SAS1] /\ step_taken'[SDP1]/\~step_taken'[SAS2]
                        THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                        ELSE /\ IF ~step_taken'[SAS1] /\ step_taken'[SAS2]
                                   THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED conforming
       /\ step_considered' = [step_considered EXCEPT ![SAS2] = TRUE]
       /\ pc' = [pc EXCEPT ![LITECOIN] = "AS3"]
       /\ UNCHANGED << hashkey, wallet, clock >>

AS3 == /\ pc[LITECOIN] = "AS3"
       /\ IF step_taken[SAS2]/\clock<=swap_contract["BOB"].timeout/\swap_contract["BOB"].state = ESCROW
             THEN /\ swap_contract' = [swap_contract EXCEPT !["BOB"].state = REDEEMED]
                  /\ premium' = [premium EXCEPT !["ALICE"].state = REFUNDED]
                  /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance-swap_contract'["BOB"].balance,
                                              !["ALICE"].balance = wallet["ALICE"].balance + swap_contract'["BOB"].balance]
                  /\ step_taken' = [step_taken EXCEPT ![SAS3] = TRUE]
             ELSE /\ IF step_taken[SAS2] /\swap_contract["BOB"].state = ESCROW
                        THEN /\ swap_contract' = [swap_contract EXCEPT !["BOB"].state = REFUNDED]
                             /\ premium' = [premium EXCEPT !["ALICE"].state = LOST]
                             /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance+premium'["ALICE"].balance,
                                                         !["ALICE"].balance = wallet["ALICE"].balance-premium'["ALICE"].balance]
                        ELSE /\ TRUE
                             /\ UNCHANGED << swap_contract, premium, wallet >>
                  /\ UNCHANGED step_taken
       /\ IF ~step_considered[SAS2]/\clock<=swap_contract'["BOB"].deadline
             THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
             ELSE /\ IF step_taken'[SAS2]/\~step_taken'[SAS3]
                        THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                        ELSE /\ IF ~step_taken'[SAS2]/\step_taken'[SAS3]
                                   THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED conforming
       /\ step_considered' = [step_considered EXCEPT ![SAS3] = TRUE]
       /\ pc' = [pc EXCEPT ![LITECOIN] = "Done"]
       /\ UNCHANGED << hashkey, clock >>

litecoin == DP1 \/ AS2 \/ AS3

tik == /\ pc[CLOCK] = "tik"
       /\ IF (clock <LIMIT)
             THEN /\ pc' = [pc EXCEPT ![CLOCK] = "tok"]
             ELSE /\ pc' = [pc EXCEPT ![CLOCK] = "Done"]
       /\ UNCHANGED << swap_contract, premium, hashkey, wallet, clock, 
                       step_taken, step_considered, conforming >>

tok == /\ pc[CLOCK] = "tok"
       /\ clock' = clock + 1
       /\ pc' = [pc EXCEPT ![CLOCK] = "tik"]
       /\ UNCHANGED << swap_contract, premium, hashkey, wallet, step_taken, 
                       step_considered, conforming >>

Clock == tik \/ tok

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == bitcoin \/ litecoin \/ Clock
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(bitcoin)
        /\ WF_vars(litecoin)
        /\ WF_vars(Clock)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-da2c0d11a0e55033d587c11f6ad84c88
====
