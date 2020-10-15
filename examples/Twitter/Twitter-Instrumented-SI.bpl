// Twitter Application
// It has 3 transactions: register, fellowUser, and addTweet
// Non-robustness check between PC and SI
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

var {:layer 0,2} copyRegistredUsers: [Uid]bool;
var {:layer 0,2} copyUserPassword: [Uid]int;

var {:layer 0,2} hb : bool;

var {:layer 0,2} att : bool;

var {:layer 0,2} hbd: [Pid][Uid]int; // to track dependency access to the table RegistredUsers

var {:layer 0,2} varAtt : Uid;

const unique lda, sta: int;

axiom ((lda == 1) && (sta == 2));

const unique attPid : Pid;
const unique helperPid : Pid;

const unique UNIL0: Uid;

///////////////////////////////////////////////////////////////////////////////
function {:builtin "((as const (Array Int Int)) 0)"} I0() returns ([Uid] int);
function {:builtin "((as const (Array Int Bool)) False)"} I1() returns ([Uid] bool);
///////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Procedure of a process
////////////////////////////////////////////////////////////////////////////////	
	
procedure {:yields} {:layer 2} process({:linear "pid"} pid:Pid, uid: Uid)
requires {:layer 2} (pid == attPid || pid == helperPid);
{
    var password     : int;
  
    assume (uid != UNIL0 && password != 0);
  
    yield;
    call Init();
    assert  {:layer 2}   (att == false);
    assert  {:layer 2}   (hb == false);
    assert  {:layer 2}   (forall pid0:Pid, uid0:Uid::  hbd[pid0][uid0] == 0);

    yield;
	assert {:layer 2}  (pid == attPid ==> hbd[pid][varAtt] != lda);
	assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt] != lda);	
	assert  {:layer 2} (pid == attPid ==> !att);
	assert  {:layer 2} (!att ==> (forall pid0:Pid, uid0:Uid::   hbd[pid0][uid0] == 0));
		
    if(*)
    {
	  	assert {:layer 2}  (pid == attPid ==> hbd[pid][varAtt] != lda);
	    assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt] != lda);	

	    call Register(pid, uid,password);

	    assert {:layer 2}  (pid == helperPid ==> hbd[pid][varAtt] != lda);	           
    }	
    yield;
}

///////////////////////////////////////////////////////////////////////////////
/// An init procedure for initializing the auxiliary variables
///////////////////////////////////////////////////////////////////////////////

procedure  {:atomic} {:layer 2}  init()
{
  assume !hb;
  assume (varAtt == UNIL0 && !att);
  assume (forall pid:Pid, uid:Uid::  hbd[pid][uid] == 0) ; 
  
}
  
procedure  {:yields} {:layer 1} {:refines "init"}  Init();
ensures {:layer 1} !hb;
ensures {:layer 1} (varAtt == UNIL0 && !att);
ensures {:layer 1} (forall pid:Pid, uid:Uid::  hbd[pid][uid] == 0) ;

///////////////////////////////////////////////////////////////////////////////
/// The instrumented Twitter transactions
///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  register(pid:Pid, uid:Uid, p: int)
modifies RegistredUsers, UserPassword;
modifies copyRegistredUsers, copyUserPassword;
modifies hbd, hb, att, varAtt;
{  
    assume (!RegistredUsers[uid] &&  p != 0);

    if (pid == attPid && !att)
	{ 
			
        att := true;
		copyRegistredUsers[uid] := true; 
        copyUserPassword[uid] := p;
		
        varAtt := uid;

		hbd[attPid][uid] := lda;
			
	}			
	else if ((pid == helperPid) && att && !hb)
	{								
		assume (hbd[attPid][uid] >= lda);

        RegistredUsers[uid] := true; 
        UserPassword[uid] := p;
	
		hb := true;

        hbd[helperPid][uid] := lda;		
	}

	else 
	{
	    RegistredUsers[uid] := true; 
        UserPassword[uid] := p;
	}
    
}
procedure{:yields}{:layer 1} {:refines "register"} Register(pid:Pid, uid:Uid, p: int);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  fellowUser({:linear "uid"} uid1:Uid, uid2:Uid)
modifies UserFollow;
{  
    assume (!UserFollow[uid1][uid2] && RegistredUsers[uid1] && RegistredUsers[uid2] && uid1 != uid2);
    
	UserFollow[uid1][uid2] := true; 
}
procedure{:yields}{:layer 1} {:refines "fellowUser"} FellowUser({:linear "uid"} uid1:Uid, uid2:Uid);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  addTweet({:linear "uid"} uid:Uid, tweet: int)
modifies UserTweetFollowers;
{  
    var copyTweet1, copyTweet2 : [Uid]int;	

    assume (RegistredUsers[uid] && tweet != 0);
      
    copyTweet1 := UserTweetFollowers[uid];
	UserTweetFollowers[uid]  := copyTweet2;

    assume(forall uid0:Uid :: UserFollow[uid0][uid] ==> (UserTweetFollowers[uid][uid0] == copyTweet1[uid0]  + tweet));

    assume(forall uid0:Uid :: !UserFollow[uid0][uid] ==> (UserTweetFollowers[uid][uid0] == copyTweet1[uid0])); 
}
procedure{:yields}{:layer 1} {:refines "addTweet"} AddTweet({:linear "uid"} uid:Uid, tweet: int);