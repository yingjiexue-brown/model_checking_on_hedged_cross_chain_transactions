------------------------- MODULE two_party -------------------------

EXTENDS Integers, TLC
(* --algorithm example

\* Assuming there are two separate contracts on each blockchain describing sequentialized designitated actions on that blockchain 
\* Then, on each blockchain, the party should behave as that asset specifies,
\* otherwise, they are regarded as silent since the asset only allow expected "input" which are asset asset escrow, asset asset redeem, etc.
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
   \* a smart contract has two sub_contract: asset_contract which monitors asset to swap and premium_contract which monitors premiums
    \* An asset_contract has balance, timeout is initialized as -1 and will be changed after it is escrowed
    \* a deadline to escrow assets
    \* a timestamp recording when it is escrowed, initialized as LIMIT
    
    asset_contract = [ALICE |-> [balance |->100, timeout |-> -1, state |-> INIT,deadline |-> 2, timestamp |-> LIMIT],
                BOB|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 3, timestamp |-> LIMIT]],
    
    \* A premium_contract has balance, timeout is initialized as -1 and will be changed after premium is deposited;
    \* a deadline to deposit the premium, a timestamp recording when it is deposited, initialized as LIMIT
    premium_contract = [ALICE |-> [balance|->2, timeout |-> -1, state |-> INIT,deadline |-> 0, timestamp |-> LIMIT],
               BOB|->[balance|->1, timeout |->-1, state |-> INIT,deadline |-> 1, timestamp |-> LIMIT]],
    \* B2A stands for the arc B2A, A2B stands for the arc A2B
    hashkey = [B2A|-> [deadline|->4,state|->INIT],A2B|->[deadline|->5,state|->INIT]],
    \* wallet contains amount of assets in this protocol
    wallet = [ALICE |-> [balance|->102,init|->102], BOB|-> [balance|->101,init|->101]],
    \* global clock
    clock = 0,
    \* step only indicates if one single step is executed according to the protocol  or not
    step_taken = [s \in STEPS |->FALSE],
    \* step_considered indicates if one step is considered, no matter this step is taken according to the protocol or skipped
    step_considered = [s \in STEPS |->FALSE],
    conforming = [p \in  PARTIES |->TRUE],
define
 INIT == 0 ESCROW == 1 REDEEMED == 2 REFUNDED == 3 LOST ==4 RELEASED == 5 \* contract states
 ALICE == 0 BOB == 1  \* ID for parties
 BITCOIN == 0 LITECOIN ==1 CLOCK == 2     \* process ids
 LIMIT == 6                         \* max clock value
 PARTIES == {ALICE, BOB}            \* parties
 SDP1 == 0  SDP2 == 1 SAS1 ==2 SAS2==3 SAS3==4 SAS4==5 \* index for each step
 STEPS == {SDP1, SDP2,SAS1,SAS2,SAS3,SAS4} 
 ending == /\step_considered[SAS4]/\step_considered[SAS3]
 
 \* properties that we are interested to check
 
 liveness == (/\ending/\conforming[ALICE]/\conforming[BOB])=>(/\premium_contract["ALICE"].state=REFUNDED /\premium_contract["BOB"].state=REFUNDED/\asset_contract["ALICE"].state=REDEEMED /\asset_contract["BOB"].state=REDEEMED)
 \* hedged
 compensated_alice == (/\ending/\conforming[ALICE]/\asset_contract["ALICE"].state=REFUNDED) => wallet["ALICE"].balance>=wallet["ALICE"].init+1
 compensated_bob == (/\ending/\conforming[BOB]/\asset_contract["BOB"].state=REFUNDED) => wallet["BOB"].balance>=wallet["BOB"].init+1
 \* safety
 safe_alice == (/\ending/\conforming[ALICE]) => wallet["ALICE"].balance>=wallet["ALICE"].init
 safe_bob == (/\ending/\conforming[BOB]) => wallet["BOB"].balance>=wallet["BOB"].init
 
end define;
\*=================bitcoin process========================================
fair process bitcoin = BITCOIN begin 

    DP2: \*clock <=1, BOB deposits his premium
    
    if clock<= premium_contract["BOB"].deadline /\ premium_contract["BOB"].state=INIT then \*otherwise, Bob cannot do anything
               premium_contract["BOB"].state:=ESCROW 
              || premium_contract["BOB"].timestamp:=clock
              ||premium_contract["BOB"].timeout:=asset_contract["ALICE"].deadline;
              step_taken[SDP2]:= TRUE;
    end if;
    
    \* this part determines if a party is conforming
    if   ~step_considered[SDP1]/\ clock<= premium_contract["ALICE"].deadline then \*  if the previous step in the protocol is not traversed or deadline
         conforming[BOB]:=FALSE;
    elsif step_taken[SDP1]/\~step_taken[SDP2] then
          conforming[BOB]:=FALSE;
    elsif ~step_taken[SDP1]/\step_taken[SDP2] then
         conforming[BOB]:=FALSE; 
    end if;
    
    step_considered[SDP2]:=TRUE;
    

    AS1:\*clock <=2, Alice publishes her asset_contract

    if step_taken[SDP2] /\ clock <= asset_contract["ALICE"].deadline /\ asset_contract["ALICE"].state = INIT then \*if DP2 finishes, Alice can choose to escrow her swap asset or not to escrow
           asset_contract["ALICE"].state := ESCROW
           ||asset_contract["ALICE"].timestamp := clock
           ||asset_contract["ALICE"].timeout := hashkey["A2B"].deadline;
           step_taken[SAS1]:= TRUE;
     
    elsif  premium_contract["BOB"].state=ESCROW then
           premium_contract["BOB"].state:=REFUNDED;
    end if;
    
  
  
    if ~step_considered[SDP2]/\ clock<= premium_contract["BOB"].deadline then
         conforming[ALICE]:=FALSE;
    elsif step_taken[SDP2]/\~step_taken[SAS1] then \* precondition satisfied
         conforming[ALICE]:=FALSE;
    elsif ~step_taken[SDP2]/\step_taken[SAS1] then \* precondition not satisfied
         conforming[ALICE]:=FALSE;
    end if;
    
    step_considered[SAS1]:=TRUE;
    
    

    AS4:\*clock<=5, Bob redeems
    if  step_taken[SAS1]/\clock<=asset_contract["ALICE"].timeout/\ asset_contract["ALICE"].state= ESCROW then \* note that we do not require as3 to finish to finish as4
        asset_contract["ALICE"].state:= REDEEMED;
        if  premium_contract["BOB"].state=ESCROW then
        premium_contract["BOB"].state:=REFUNDED;
        end if;
        wallet["BOB"].balance:=wallet["BOB"].balance +asset_contract["ALICE"].balance
        ||wallet["ALICE"].balance:=wallet["ALICE"].balance-asset_contract["ALICE"].balance;
        step_taken[SAS4]:= TRUE;
       
    elsif step_taken[SAS1]/\ asset_contract["ALICE"].state= ESCROW then \* Bob is too late
         asset_contract["ALICE"].state := REFUNDED;
         if  premium_contract["BOB"].state=ESCROW then
         premium_contract["BOB"].state:=LOST;
         wallet["BOB"].balance := wallet["BOB"].balance-premium_contract["BOB"].balance
         ||wallet["ALICE"].balance := wallet["ALICE"].balance+premium_contract["BOB"].balance;
         end if;
    end if;
    
    \* this part determines the whether they are conforming 
    if  ~step_taken[SAS3]/\step_taken[SAS2]/\ step_taken[SAS4] then
          conforming[ALICE]:= FALSE; 
    elsif ~step_considered[SAS3] /\ clock<=hashkey["B2A"].deadline then
          conforming[BOB]:= FALSE; 
    elsif step_taken[SAS3]/\step_taken[SAS1]/\~step_taken[SAS4] then
          conforming[BOB]:= FALSE; 
    end if;
    
    step_considered[SAS4]:=TRUE;
end process
\*=================litcoin process========================================
fair process litecoin=LITECOIN begin

    DP1:\* clock=0, Alice deposits her premium
    if clock<=premium_contract["ALICE"].deadline /\ premium_contract["ALICE"].state=INIT then \* otherwise, LTC blockchain does not accept escrow, i.e. alice is silent or she is too late
               premium_contract["ALICE"].timestamp:=clock 
               || premium_contract["ALICE"].state:=ESCROW
               ||premium_contract["ALICE"].timeout:=asset_contract["BOB"].deadline; \*premium_contract["ALICE"] timeouts if asset_contract["BOB"]is not published before deadline
               step_taken[SDP1]:= TRUE;       
    
    end if;

    \* this part determines if a party is conforming
    if    ~step_taken[SDP1] then
         conforming[ALICE]:= FALSE;
    end if;
    
    step_considered[SDP1]:=TRUE;
    
    

    AS2:\* clock <=3, Bob publishes his swap asset
    if step_taken[SDP1] /\ clock<=asset_contract["BOB"].deadline /\  asset_contract["BOB"].state = INIT then
                asset_contract["BOB"].state := ESCROW
                ||asset_contract["BOB"].timestamp := clock
                ||asset_contract["BOB"].timeout:=hashkey["B2A"].deadline;
                step_taken[SAS2]:=TRUE;
    
    elsif premium_contract["ALICE"].state=ESCROW then
          premium_contract["ALICE"].state:= REFUNDED;
    end if;
    
    \* this part determines if a party is conforming
    if  ~step_considered[SAS1] /\ clock<=asset_contract["ALICE"].deadline then
         conforming[BOB]:=FALSE;
    elsif step_taken[SAS1] /\ step_taken[SDP1]/\~step_taken[SAS2] then \* precondition satisfied
         conforming[BOB]:=FALSE;
    elsif ~step_taken[SAS1] /\ step_taken[SAS2] then \* precondition not satisfied
        conforming[BOB]:=FALSE;
    end if;

    step_considered[SAS2]:=TRUE;

    AS3:\*clock<=4, Alice redeems Bob's asset
    
    if step_taken[SAS2]/\clock<=asset_contract["BOB"].timeout/\asset_contract["BOB"].state = ESCROW then
                asset_contract["BOB"].state := REDEEMED;
               if  premium_contract["ALICE"].state=ESCROW then
               premium_contract["ALICE"].state:=REFUNDED;
               end if;
               wallet["BOB"].balance := wallet["BOB"].balance-asset_contract["BOB"].balance \*Bob loses $100
               ||wallet["ALICE"].balance := wallet["ALICE"].balance + asset_contract["BOB"].balance;\*alice gets $100
               step_taken[SAS3]:=TRUE;
     
    elsif step_taken[SAS2] /\asset_contract["BOB"].state = ESCROW then \* Alice is too late
           asset_contract["BOB"].state := REFUNDED;
            if  premium_contract["ALICE"].state=ESCROW then
           premium_contract["ALICE"].state:=LOST;
           wallet["BOB"].balance := wallet["BOB"].balance+premium_contract["ALICE"].balance
           ||wallet["ALICE"].balance := wallet["ALICE"].balance-premium_contract["ALICE"].balance
           end if;
    end if;
  
    \* this part determines if a party is conforming and the protocol goes well
    if ~step_considered[SAS2]/\clock<=asset_contract["BOB"].deadline then
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-473e7ebcfc6a5f70208154912c4629c1
VARIABLES asset_contract, premium_contract, hashkey, wallet, clock, 
          step_taken, step_considered, conforming, pc

(* define statement *)
INIT == 0 ESCROW == 1 REDEEMED == 2 REFUNDED == 3 LOST ==4 RELEASED == 5
ALICE == 0 BOB == 1
BITCOIN == 0 LITECOIN ==1 CLOCK == 2
LIMIT == 6
PARTIES == {ALICE, BOB}
SDP1 == 0  SDP2 == 1 SAS1 ==2 SAS2==3 SAS3==4 SAS4==5
STEPS == {SDP1, SDP2,SAS1,SAS2,SAS3,SAS4}
ending == /\step_considered[SAS4]/\step_considered[SAS3]



liveness == (/\ending/\conforming[ALICE]/\conforming[BOB])=>(/\premium_contract["ALICE"].state=REFUNDED /\premium_contract["BOB"].state=REFUNDED/\asset_contract["ALICE"].state=REDEEMED /\asset_contract["BOB"].state=REDEEMED)

compensated_alice == (/\ending/\conforming[ALICE]/\asset_contract["ALICE"].state=REFUNDED) => wallet["ALICE"].balance>=wallet["ALICE"].init+1
compensated_bob == (/\ending/\conforming[BOB]/\asset_contract["BOB"].state=REFUNDED) => wallet["BOB"].balance>=wallet["BOB"].init+1

safe_alice == (/\ending/\conforming[ALICE]) => wallet["ALICE"].balance>=wallet["ALICE"].init
safe_bob == (/\ending/\conforming[BOB]) => wallet["BOB"].balance>=wallet["BOB"].init


vars == << asset_contract, premium_contract, hashkey, wallet, clock, 
           step_taken, step_considered, conforming, pc >>

ProcSet == {BITCOIN} \cup {LITECOIN} \cup {CLOCK}

Init == (* Global variables *)
        /\ asset_contract =      [ALICE |-> [balance |->100, timeout |-> -1, state |-> INIT,deadline |-> 2, timestamp |-> LIMIT],
                            BOB|->[balance |->100,timeout |-> -1, state |-> INIT,deadline |-> 3, timestamp |-> LIMIT]]
        /\ premium_contract =         [ALICE |-> [balance|->2, timeout |-> -1, state |-> INIT,deadline |-> 0, timestamp |-> LIMIT],
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
       /\ IF clock<= premium_contract["BOB"].deadline /\ premium_contract["BOB"].state=INIT
             THEN /\ premium_contract' = [premium_contract EXCEPT !["BOB"].state = ESCROW,
                                                                  !["BOB"].timestamp = clock,
                                                                  !["BOB"].timeout = asset_contract["ALICE"].deadline]
                  /\ step_taken' = [step_taken EXCEPT ![SDP2] = TRUE]
             ELSE /\ TRUE
                  /\ UNCHANGED << premium_contract, step_taken >>
       /\ IF ~step_considered[SDP1]/\ clock<= premium_contract'["ALICE"].deadline
             THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
             ELSE /\ IF step_taken'[SDP1]/\~step_taken'[SDP2]
                        THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                        ELSE /\ IF ~step_taken'[SDP1]/\step_taken'[SDP2]
                                   THEN /\ conforming' = [conforming EXCEPT ![BOB] = FALSE]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED conforming
       /\ step_considered' = [step_considered EXCEPT ![SDP2] = TRUE]
       /\ pc' = [pc EXCEPT ![BITCOIN] = "AS1"]
       /\ UNCHANGED << asset_contract, hashkey, wallet, clock >>

AS1 == /\ pc[BITCOIN] = "AS1"
       /\ IF step_taken[SDP2] /\ clock <= asset_contract["ALICE"].deadline /\ asset_contract["ALICE"].state = INIT
             THEN /\ asset_contract' = [asset_contract EXCEPT !["ALICE"].state = ESCROW,
                                                              !["ALICE"].timestamp = clock,
                                                              !["ALICE"].timeout = hashkey["A2B"].deadline]
                  /\ step_taken' = [step_taken EXCEPT ![SAS1] = TRUE]
                  /\ UNCHANGED premium_contract
             ELSE /\ IF premium_contract["BOB"].state=ESCROW
                        THEN /\ premium_contract' = [premium_contract EXCEPT !["BOB"].state = REFUNDED]
                        ELSE /\ TRUE
                             /\ UNCHANGED premium_contract
                  /\ UNCHANGED << asset_contract, step_taken >>
       /\ IF ~step_considered[SDP2]/\ clock<= premium_contract'["BOB"].deadline
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
       /\ IF step_taken[SAS1]/\clock<=asset_contract["ALICE"].timeout/\ asset_contract["ALICE"].state= ESCROW
             THEN /\ asset_contract' = [asset_contract EXCEPT !["ALICE"].state = REDEEMED]
                  /\ IF premium_contract["BOB"].state=ESCROW
                        THEN /\ premium_contract' = [premium_contract EXCEPT !["BOB"].state = REFUNDED]
                        ELSE /\ TRUE
                             /\ UNCHANGED premium_contract
                  /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance +asset_contract'["ALICE"].balance,
                                              !["ALICE"].balance = wallet["ALICE"].balance-asset_contract'["ALICE"].balance]
                  /\ step_taken' = [step_taken EXCEPT ![SAS4] = TRUE]
             ELSE /\ IF step_taken[SAS1]/\ asset_contract["ALICE"].state= ESCROW
                        THEN /\ asset_contract' = [asset_contract EXCEPT !["ALICE"].state = REFUNDED]
                             /\ IF premium_contract["BOB"].state=ESCROW
                                   THEN /\ premium_contract' = [premium_contract EXCEPT !["BOB"].state = LOST]
                                        /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance-premium_contract'["BOB"].balance,
                                                                    !["ALICE"].balance = wallet["ALICE"].balance+premium_contract'["BOB"].balance]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << premium_contract, 
                                                        wallet >>
                        ELSE /\ TRUE
                             /\ UNCHANGED << asset_contract, premium_contract, 
                                             wallet >>
                  /\ UNCHANGED step_taken
       /\ IF ~step_taken'[SAS3]/\step_taken'[SAS2]/\ step_taken'[SAS4]
             THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
             ELSE /\ IF ~step_considered[SAS3] /\ clock<=hashkey["B2A"].deadline
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
       /\ IF clock<=premium_contract["ALICE"].deadline /\ premium_contract["ALICE"].state=INIT
             THEN /\ premium_contract' = [premium_contract EXCEPT !["ALICE"].timestamp = clock,
                                                                  !["ALICE"].state = ESCROW,
                                                                  !["ALICE"].timeout = asset_contract["BOB"].deadline]
                  /\ step_taken' = [step_taken EXCEPT ![SDP1] = TRUE]
             ELSE /\ TRUE
                  /\ UNCHANGED << premium_contract, step_taken >>
       /\ IF ~step_taken'[SDP1]
             THEN /\ conforming' = [conforming EXCEPT ![ALICE] = FALSE]
             ELSE /\ TRUE
                  /\ UNCHANGED conforming
       /\ step_considered' = [step_considered EXCEPT ![SDP1] = TRUE]
       /\ pc' = [pc EXCEPT ![LITECOIN] = "AS2"]
       /\ UNCHANGED << asset_contract, hashkey, wallet, clock >>

AS2 == /\ pc[LITECOIN] = "AS2"
       /\ IF step_taken[SDP1] /\ clock<=asset_contract["BOB"].deadline /\  asset_contract["BOB"].state = INIT
             THEN /\ asset_contract' = [asset_contract EXCEPT !["BOB"].state = ESCROW,
                                                              !["BOB"].timestamp = clock,
                                                              !["BOB"].timeout = hashkey["B2A"].deadline]
                  /\ step_taken' = [step_taken EXCEPT ![SAS2] = TRUE]
                  /\ UNCHANGED premium_contract
             ELSE /\ IF premium_contract["ALICE"].state=ESCROW
                        THEN /\ premium_contract' = [premium_contract EXCEPT !["ALICE"].state = REFUNDED]
                        ELSE /\ TRUE
                             /\ UNCHANGED premium_contract
                  /\ UNCHANGED << asset_contract, step_taken >>
       /\ IF ~step_considered[SAS1] /\ clock<=asset_contract'["ALICE"].deadline
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
       /\ IF step_taken[SAS2]/\clock<=asset_contract["BOB"].timeout/\asset_contract["BOB"].state = ESCROW
             THEN /\ asset_contract' = [asset_contract EXCEPT !["BOB"].state = REDEEMED]
                  /\ IF premium_contract["ALICE"].state=ESCROW
                        THEN /\ premium_contract' = [premium_contract EXCEPT !["ALICE"].state = REFUNDED]
                        ELSE /\ TRUE
                             /\ UNCHANGED premium_contract
                  /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance-asset_contract'["BOB"].balance,
                                              !["ALICE"].balance = wallet["ALICE"].balance + asset_contract'["BOB"].balance]
                  /\ step_taken' = [step_taken EXCEPT ![SAS3] = TRUE]
             ELSE /\ IF step_taken[SAS2] /\asset_contract["BOB"].state = ESCROW
                        THEN /\ asset_contract' = [asset_contract EXCEPT !["BOB"].state = REFUNDED]
                             /\ IF premium_contract["ALICE"].state=ESCROW
                                   THEN /\ premium_contract' = [premium_contract EXCEPT !["ALICE"].state = LOST]
                                        /\ wallet' = [wallet EXCEPT !["BOB"].balance = wallet["BOB"].balance+premium_contract'["ALICE"].balance,
                                                                    !["ALICE"].balance = wallet["ALICE"].balance-premium_contract'["ALICE"].balance]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << premium_contract, 
                                                        wallet >>
                        ELSE /\ TRUE
                             /\ UNCHANGED << asset_contract, premium_contract, 
                                             wallet >>
                  /\ UNCHANGED step_taken
       /\ IF ~step_considered[SAS2]/\clock<=asset_contract'["BOB"].deadline
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
       /\ UNCHANGED << asset_contract, premium_contract, hashkey, wallet, 
                       clock, step_taken, step_considered, conforming >>

tok == /\ pc[CLOCK] = "tok"
       /\ clock' = clock + 1
       /\ pc' = [pc EXCEPT ![CLOCK] = "tik"]
       /\ UNCHANGED << asset_contract, premium_contract, hashkey, wallet, 
                       step_taken, step_considered, conforming >>

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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-700c49ba814da733f5c329b2606f6ef9

====
