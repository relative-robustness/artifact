// Vote Application
// Instead of having the number of votes per given pnb to be less than some maxNbVotes value
// in order to cast new vote we have that in order to cast new votes there must 
// exist two placement in the table VoterPhoneToVotesCount that are empty
// It has 1 transaction
// Non-robustness check between SI and Serializability
// RUN: /usr/bin/time -v --format="%e" %boogie -noinfer -typeEncoding:m -tracePOs -traceTimes  -trace  -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Pid;

type Cid;            // Contestant identifier
type Vid;           // Vote identifier
type Pnb;          // Phone number 
type Sid;         // State identifier
type Acd;        // Area code

function {:builtin "MapConst"} MapConstBool(bool) : [Pid]bool;
function {:inline} {:linear "pid"} PidCollector(x: Pid) : [Pid]bool
{
  MapConstBool(false)[x := true]
}

function {:builtin "MapConst"} MapConstBool2(bool) : [Vid]bool;
function {:inline} {:linear "vid"} VidCollector(x: Vid) : [Vid]bool
{
  MapConstBool2(false)[x := true]
}

var {:layer 0,2} ActiveContestant: [Cid]bool;
var {:layer 0,2} AreaToState: [Acd]Sid;
var {:layer 0,2} VoterPhoneToVotesCount: [Pnb][Vid]int;
var {:layer 0,2} VidValid: [Vid]bool;
var {:layer 0,2} VotesPnb: [Vid]Pnb;
var {:layer 0,2} VotesSid: [Vid]Sid;
var {:layer 0,2} VotesCid: [Vid]Cid;

//////////////////////////////////////////////
// Auxiliary variables for the instrumentation:
//////////////////////////////////////////////

var {:layer 0,2} copyActiveContestant: [Cid]bool;
var {:layer 0,2} copyAreaToState: [Acd]Sid;
var {:layer 0,2} copyVoterPhoneToVotesCount: [Pnb][Vid]int;
var {:layer 0,2} copyVidValid: [Vid]bool;
var {:layer 0,2} copyVotesPnb: [Vid]Pnb;
var {:layer 0,2} copyVotesSid: [Vid]Sid;
var {:layer 0,2} copyVotesCid: [Vid]Cid;

var {:layer 0,2} hb : bool;

var {:layer 0,2} att : bool;

var {:layer 0,2} hbd: [Pid][Pnb][Vid]int;  // Add hbd to track access to VoterPhoneToVotesCount 
                                      // by a given pnb and the addition of new vote with the pnb

var {:layer 0,2} varAtt1 : Pnb;
var {:layer 0,2} varAtt2 : Vid;

const unique lda, sta: int;

axiom ((lda == 1) && (sta == 2));

const unique attPid : Pid;
const unique helperPid : Pid;

const unique vid1 : Vid;
const unique vid2 : Vid;

const unique PNIL0: Pnb;
const unique VNIL0: Vid;

axiom ((vid1 != VNIL0) && (vid2 != VNIL0));

////////////////////////////////////////////////////////////////////////////////
// Procedure of a process
////////////////////////////////////////////////////////////////////////////////
	
procedure {:yields} {:layer 2} process({:linear "pid"} pid:Pid, {:linear "vid"} vid:Vid)
requires {:layer 2} ((pid == attPid  && vid == vid1)|| (pid == helperPid && vid == vid2));
{
     var pnb0:Pnb;
     var cid0:Cid;
     var acd0:Acd; 
  
    assume (pnb0 != PNIL0);
  
    yield;
    call Init();
    assert  {:layer 2}   (att == false);
    assert  {:layer 2}   (hb == false);
    assert  {:layer 2}   (forall pid0:Pid, pnb:Pnb, vid0:Vid::  hbd[pid0][pnb][vid0] == 0);

   
    yield;
	  assert {:layer 2}  (pid == attPid ==> hbd[pid][varAtt1][varAtt2] != lda);
	  assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);	
	  assert  {:layer 2} (pid == attPid ==> !att);
	  assert  {:layer 2} (!att ==> (forall pid0:Pid, pnb:Pnb, vid0:Vid::  hbd[pid0][pnb][vid0] == 0));

	if(pid == attPid)
    {       

		  	assert {:layer 2}  (pid == attPid ==> hbd[pid][varAtt1][varAtt2] != lda);
	      assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);	
	      assert  {:layer 2} (pid == attPid ==> !att);
	      assert  {:layer 2} (!att ==> (forall pid0:Pid, pnb:Pnb, vid0:Vid::  hbd[pid0][pnb][vid0] == 0));

	      call  AddVote(pid, cid0, vid, pnb0, acd0);
		
	      assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);	
	
    }
    yield;
	      assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);	
	
	
    if(pid == helperPid)
    {
	      assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);		
		   
	    call  AddVote(pid, cid0, vid, pnb0, acd0);
      
	      assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);	
    }
	
    yield;
}

///////////////////////////////////////////////////////////////////////////////
/// An init procedure for initializing the auxiliary variables
///////////////////////////////////////////////////////////////////////////////

procedure  {:atomic} {:layer 2}  init()
{
  assume !hb;
  assume (varAtt1 == PNIL0 && varAtt2 == VNIL0 && !att);
  assume (forall pid:Pid, pnb:Pnb, vid:Vid::  hbd[pid][pnb][vid] == 0) ; 
  
}
  
procedure  {:yields} {:layer 1} {:refines "init"}  Init();
ensures {:layer 1} !hb;
ensures {:layer 1} (varAtt1 == PNIL0 && varAtt2 == VNIL0 && !att);
ensures {:layer 1} (forall pid:Pid, pnb:Pnb, vid:Vid::  hbd[pid][pnb][vid] == 0) ;

///////////////////////////////////////////////////////////////////////////////
/// The instrumented Vote transaction
///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  addVote(pid:Pid, cid:Cid, {:linear "vid"} vid: Vid, pnb: Pnb, acd: Acd)
modifies VidValid, VotesCid, VotesPnb, VotesSid, VoterPhoneToVotesCount;
modifies copyVidValid, copyVotesCid, copyVotesPnb, copyVotesSid, copyVoterPhoneToVotesCount;
modifies hbd, hb, att, varAtt1, varAtt2;
{  

  var hbd1: [Pnb][Vid]int;

  assume(!VidValid[vid]);

  assume (ActiveContestant[cid] && VoterPhoneToVotesCount[pnb][vid] == 0 && 
          (exists vid0:Vid:: vid0 != vid && VoterPhoneToVotesCount[pnb][vid0] == 0));

  if (pid == attPid && !att)
	{ 
	    	copyVidValid[vid] := true;
		    copyVotesCid[vid] := cid;
        copyVotesPnb[vid] := pnb;
        copyVotesSid[vid] := AreaToState[acd];
        copyVoterPhoneToVotesCount[pnb][vid] := 1;
		
        varAtt1 := pnb;
        varAtt2 := vid;

        att := true;

        hbd[attPid] := hbd1; 
        assume (forall pnb0:Pnb, vid0:Vid:: hbd[attPid][pnb0][vid0] == lda);		
	}			
	else if ((pid == helperPid) && att && !hb)
	{								
		  assume (hbd[attPid][pnb][vid] >= lda);

      VidValid[vid] := true;
		  VotesCid[vid] := cid;
      VotesPnb[vid] := pnb;
      VotesSid[vid] := AreaToState[acd];
      VoterPhoneToVotesCount[pnb][vid] := 1;
	
		  hb := true;

      hbd[helperPid] := hbd1; 
      assume (forall pnb0:Pnb, vid0:Vid:: hbd[helperPid][pnb0][vid0] == lda);		

      hbd[helperPid][pnb][vid] := sta;	

      assume (hbd[helperPid][varAtt1][varAtt2] != sta);	
	}

	else 
	{
	    VidValid[vid] := true;
		  VotesCid[vid] := cid;
      VotesPnb[vid] := pnb;
      VotesSid[vid] := AreaToState[acd];
      VoterPhoneToVotesCount[pnb][vid] := 1;

	}
}
procedure{:yields}{:layer 1} {:refines "addVote"} AddVote(pid:Pid, cid:Cid, {:linear "vid"} vid: Vid, pnb: Pnb, acd: Acd);