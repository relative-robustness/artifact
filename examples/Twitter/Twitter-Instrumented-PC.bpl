// Twitter Application
// It has 3 transactions: register, fellowUser, and addTweet
// Non-robustness check between CC and PC
// RUN: /usr/bin/time -v --format="%e" %boogie -noinfer -typeEncoding:m -tracePOs -traceTimes  -trace  -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Pid;
type Uid;

function {:builtin "MapConst"} MapConstBool(bool) : [Pid]bool;
function {:inline} {:linear "pid"} PidCollector(x: Pid) : [Pid]bool
{
  MapConstBool(false)[x := true]
}

function {:builtin "MapConst"} MapConstBool2(bool) : [Uid]bool;
function {:inline} {:linear "uid"} UidCollector(x: Uid) : [Uid]bool
{
  MapConstBool2(false)[x := true]
}

var {:layer 0,2} RegistredUsers: [Uid]bool;
var {:layer 0,2} UserPassword: [Uid]int;
var {:layer 0,2} UserFollow: [Uid][Uid]bool;
var {:layer 0,2} UserTweetFollowers: [Uid][Uid]int;

//////////////////////////////////////////////
// Auxiliary variables for the instrumentation:
//////////////////////////////////////////////

var {:layer 0,2} copyUserFollow: [Uid][Uid]bool;
var {:layer 0,2} copyUserTweetFollowers: [Uid][Uid]int;

var {:layer 0,2} hb : bool;

var {:layer 0,2} att : bool;

var {:layer 0,2} hbd: [Pid][Uid][Uid]int; // to track dependency access to the table UserFollow

var {:layer 0,2} varAtt1 : Uid;
var {:layer 0,2} varAtt2 : Uid;

const unique lda, sta: int;

axiom ((lda == 1) && (sta == 2));

const unique attPid : Pid;
const unique helperPid : Pid;

const unique uid01 : Uid;
const unique uid02 : Uid;

const unique UNIL0: Uid;

axiom ((uid01 != UNIL0) && (uid02 != UNIL0));

///////////////////////////////////////////////////////////////////////////////
function {:builtin "((as const (Array Int Int)) 0)"} I0() returns ([Uid] int);
function {:builtin "((as const (Array Int Bool)) False)"} I1() returns ([Uid] bool);
///////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Procedure of a process
////////////////////////////////////////////////////////////////////////////////
	
procedure {:yields} {:layer 2} process({:linear "pid"} pid:Pid, {:linear "uid"} uid1: Uid, uid2: Uid)
requires {:layer 2} ((pid == attPid && uid1 == uid01 && uid2 == uid02) || 
                     (pid == helperPid && uid1 == uid02 && uid2 == uid01));
{
    var tweet     : int;
  
    assume (tweet != 0);
  
    yield;
    call Init();
    assert  {:layer 2}   (att == false);
    assert  {:layer 2}   (hb == false);
    assert  {:layer 2}   (forall pid0:Pid, uid3:Uid, uid4:Uid::  hbd[pid0][uid3][uid4] == 0);

    yield;
	assert {:layer 2}  (pid == attPid ==> hbd[pid][varAtt1][varAtt2] != lda);
	assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);	
	assert  {:layer 2} (pid == attPid ==> !att);
	assert  {:layer 2} (!att ==> (forall pid0:Pid, uid3:Uid, uid4:Uid::  hbd[pid0][uid3][uid4] == 0));
		
    if(*)
    {
	  	assert {:layer 2}  (pid == attPid ==> hbd[pid][varAtt1][varAtt2] != lda);
	    assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);	

	    call FellowUser(pid, uid1, uid2);

	    assert {:layer 2}  (pid == attPid ==> hbd[pid][varAtt1][varAtt2] != lda);
	    assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);		           
    }	
    yield;
    assert {:layer 2}  (pid == attPid ==> hbd[pid][varAtt1][varAtt2] != lda);
	assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);

    if(*)
    {
	  	assert {:layer 2}  (pid == attPid ==> hbd[pid][varAtt1][varAtt2] != lda);
	    assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt1][varAtt2] != lda);	

	    call AddTweet(pid, uid1, tweet);

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
  assume (varAtt1 == UNIL0 && varAtt2 == UNIL0 && !att);
  assume (forall pid:Pid, uid3:Uid, uid4:Uid::  hbd[pid][uid3][uid4] == 0) ; 
  
}
  
procedure  {:yields} {:layer 1} {:refines "init"}  Init();
ensures {:layer 1} !hb;
ensures {:layer 1} (varAtt1 == UNIL0 && varAtt2 == UNIL0 && !att);
ensures {:layer 1} (forall pid:Pid, uid3:Uid, uid4:Uid::  hbd[pid][uid3][uid4] == 0) ;

///////////////////////////////////////////////////////////////////////////////
/// The instrumented Twitter transactions
///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  register(uid:Uid, p: int)
modifies RegistredUsers, UserPassword;
{  
    assume (!RegistredUsers[uid] &&  p != 0);
 
    RegistredUsers[uid] := true; 
    UserPassword[uid] := p;  
}
procedure{:yields}{:layer 1} {:refines "register"} Register(uid:Uid, p: int);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  fellowUser(pid:Pid, {:linear "uid"} uid1:Uid, uid2:Uid)
modifies UserFollow, copyUserFollow;
modifies hb, hbd, att, varAtt1, varAtt2;
{  
    assume (!UserFollow[uid1][uid2] && RegistredUsers[uid1] && RegistredUsers[uid2] && uid1 != uid2);

    if (pid == attPid && !att)
	{ 
			
        att := true;

		copyUserFollow[uid1][uid2] := true;
		
        varAtt1 := uid1;
        varAtt2 := uid2;			
	}			
	else if ((pid == helperPid) && att && !hb)
	{								
		assume (hbd[attPid][uid1][uid2] >= lda);

        UserFollow[uid1][uid2] := true;
	
		hb := true;

        hbd[helperPid][uid1][uid2] := sta;		
	}
	else 
	{
	    UserFollow[uid1][uid2] := true;
	}	 
}
procedure{:yields}{:layer 1} {:refines "fellowUser"} FellowUser(pid:Pid, {:linear "uid"} uid1:Uid, uid2:Uid);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  addTweet(pid:Pid, {:linear "uid"} uid:Uid, tweet: int)
modifies UserTweetFollowers, copyUserTweetFollowers;
modifies hbd;
{  
    var copyTweet1, copyTweet2 : [Uid]int;	
    var hbd1 : [Uid][Uid]int;
    var hbd2 : [Uid][Uid]int;

    assume (RegistredUsers[uid] && tweet != 0);

    if (pid == attPid && att)
	{ 
			
        copyTweet1 := UserTweetFollowers[uid];
	    copyUserTweetFollowers[uid]  := copyTweet2;

        assume(forall uid0:Uid :: UserFollow[uid0][uid] ==> (copyUserTweetFollowers[uid][uid0] == copyTweet1[uid0] + tweet));

        assume(forall uid0:Uid :: !UserFollow[uid0][uid] ==> (copyUserTweetFollowers[uid][uid0] == copyTweet1[uid0])); 
		
        hbd1 := hbd[attPid];
        hbd[attPid] := hbd2; 

        assume(forall uid1:Uid, uid2:Uid :: uid2 != uid ==> hbd[attPid][uid1][uid2] == hbd1[uid1][uid2]);
        assume(forall uid1:Uid :: hbd[attPid][uid1][uid] == lda);
	}			
	else if ((pid == helperPid) && att && hb)
	{								
		copyTweet1 := UserTweetFollowers[uid];
	    UserTweetFollowers[uid]  := copyTweet2;

        assume(forall uid0:Uid :: UserFollow[uid0][uid] ==> (UserTweetFollowers[uid][uid0] == copyTweet1[uid0] + tweet));

        assume(forall uid0:Uid :: !UserFollow[uid0][uid] ==> (UserTweetFollowers[uid][uid0] == copyTweet1[uid0])); 
		
        hbd1 := hbd[helperPid];
        hbd[helperPid] := hbd2; 

        assume(forall uid1:Uid, uid2:Uid :: uid2 != uid ==> hbd[helperPid][uid1][uid2] == hbd1[uid1][uid2]);
        assume(forall uid1:Uid :: hbd[helperPid][uid1][uid] == lda);
	}

	else 
	{
	    copyTweet1 := UserTweetFollowers[uid];
	    UserTweetFollowers[uid]  := copyTweet2;

        assume(forall uid0:Uid :: UserFollow[uid0][uid] ==> (UserTweetFollowers[uid][uid0] == copyTweet1[uid0]  + tweet));

        assume(forall uid0:Uid :: !UserFollow[uid0][uid] ==> (UserTweetFollowers[uid][uid0] == copyTweet1[uid0])); 
	}	 
}
procedure{:yields}{:layer 1} {:refines "addTweet"} AddTweet(pid:Pid, {:linear "uid"} uid:Uid, tweet: int);
