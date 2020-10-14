// Epinions Application
// It has 8 transactions
// A user is represented by a single process
// Non-robustness check
// RUN: /usr/bin/time -v --format="%e" %boogie -noinfer -typeEncoding:m -tracePOs -traceTimes  -trace  -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Pid;

type Iid;            // Item identifier
type Uid;          // User identifier

type Unm;          // User Name
type Itl;         // Item Title

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


var {:layer 0,2} ActiveUser: [Uid]bool;
var {:layer 0,2} UserName: [Uid]Unm;

var {:layer 0,2} Review: [Iid][Uid]int;
var {:layer 0,2} Trust: [Uid][Uid]int;

var {:layer 0,2} ActiveItem: [Iid]bool;
var {:layer 0,2} ItemName: [Iid]Itl;

//////////////////////////////////////////////
// Auxiliary variables for the instrumentation:
//////////////////////////////////////////////

var {:layer 0,2} copyActiveUser: [Uid]bool;
var {:layer 0,2} copyUserName: [Uid]Unm;
var {:layer 0,2} copyReview: [Iid][Uid]int;
var {:layer 0,2} copyTrust: [Uid][Uid]int;
var {:layer 0,2} copyActiveItem: [Iid]bool;
var {:layer 0,2} copyItemName: [Iid]Itl;

var {:layer 0,2} hb : bool;

var {:layer 0,2} att : bool;

var {:layer 0,2} hbd: [Iid][Uid][Pid]int;


var {:layer 0,2} varAtt1 : Iid;
var {:layer 0,2} varAtt2 : Uid;


const unique lda, sta: int;

axiom ((lda == 1) && (sta == 2));


const unique attPid : Pid;
const unique helperPid : Pid;


const unique uid0 : Uid;
const unique uid1 : Uid;

axiom ((uid0 != UNIL0) && (uid1 != UNIL0));

const unique UNIL0: Uid;
const unique INIL0: Iid;

////////////////////////////////////////////////////////////////////////////////
// Procedure of a process
////////////////////////////////////////////////////////////////////////////////

procedure {:yields} {:layer 2} process({:linear "pid"} pid:Pid, {:linear "uid"} uid:Uid, rating: int)
requires {:layer 2} ((pid == attPid && uid == uid0) || (pid == helperPid && uid == uid1));
{
    var iId0 : Iid;
    var retItemRating : [Uid]int;

    assume (iId0 != INIL0);

    yield;
    call Init();
    assert  {:layer 2}   (att == false);
    assert  {:layer 2}   (hb == false);
    assert  {:layer 2}   (forall iId:Iid, uId:Uid, pid0:Pid:: hbd[iId][uId][pid0] == 0);
   
    yield;
	assert {:layer 2}  (pid == attPid ==> hbd[varAtt1][varAtt2][pid] != lda);
	assert {:layer 2}  (pid == helperPid ==> hbd[varAtt1][varAtt2][pid] != lda);	
	assert  {:layer 2} (pid == attPid ==> !att);
	assert  {:layer 2} (!att ==> (forall iId:Iid, uId:Uid, pid0:Pid:: hbd[iId][uId][pid0] == 0));
	
	call  UpdateReview(pid, iId0, uid, rating);

	assert {:layer 2}  (pid == attPid ==> hbd[varAtt1][varAtt2][pid] != lda);
	assert {:layer 2}  (pid == helperPid ==> hbd[varAtt1][varAtt2][pid] != lda);
	           
    yield;
	assert {:layer 2}  (pid == attPid ==> hbd[varAtt1][varAtt2][pid] != lda);
	assert {:layer 2}  (pid == helperPid ==> hbd[varAtt1][varAtt2][pid] != lda);	
	   
	call  retItemRating :=  GetAllRating(pid, iId0) ;
    
	assert {:layer 2}  (pid == helperPid ==> hbd[varAtt1][varAtt2][pid] != lda);

    yield;
}

///////////////////////////////////////////////////////////////////////////////
/// An init procedure for initializing the auxiliary variables
///////////////////////////////////////////////////////////////////////////////

procedure  {:atomic} {:layer 2}  init()
{
  assume !hb;
  assume (varAtt1 == INIL0 && varAtt2 == UNIL0 && !att);
  assume (forall iId:Iid, uId:Uid, pid:Pid::  hbd[iId][uId][pid] == 0); 
  
}
  
procedure  {:yields} {:layer 1} {:refines "init"}  Init();
ensures {:layer 1} !hb;
ensures {:layer 1} (varAtt1 == INIL0 && varAtt2 == UNIL0 && !att);
ensures {:layer 1} (forall iId:Iid, uId:Uid, pid:Pid::  hbd[iId][uId][pid] == 0) ;

///////////////////////////////////////////////////////////////////////////////
/// The instrumented Epinions procedures
///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  getItemReviewsByTrustedUser(iid:Iid, uid:Uid) returns (ItemReviewers : [Uid]int, TrustedUsers: [Uid]int)
{  
    assume(ActiveUser[uid] && ActiveItem[iid]);

    ItemReviewers := Review[iid] ;
    TrustedUsers := Trust[uid] ;
}
procedure{:yields}{:layer 1} {:refines "getItemReviewsByTrustedUser"} GetItemReviewsByTrustedUser(iid:Iid,  uid:Uid) returns (ItemReviewers : [Uid]int, TrustedUsers: [Uid]int) ;
ensures {:layer 1} ( (ActiveUser[uid] && ActiveItem[iid]) ==> 
                     (ItemReviewers == Review[iid] && TrustedUsers == Trust[uid]) );

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  getReviewItem(uid:Uid) returns (UserRating : [Iid]int)
{  
    assume(ActiveUser[uid]);

    assume(forall iid:Iid :: UserRating[iid] == Review[iid][uid]);
}
procedure{:yields}{:layer 1} {:refines "getReviewItem"} GetReviewItem(uid:Uid) returns (UserRating: [Iid]int) ;
ensures {:layer 1} ( ActiveUser[uid] ==> 
                     (forall iid:Iid :: UserRating[iid] == Review[iid][uid]) );

///////////////////////////////////////////////////////////////////////////////

//getAverageRating
//getAllRating
procedure {:atomic}{:layer 2}  getAllRating({:linear "pid"} pid:Pid, iid: Iid) returns (ItemRating : [Uid]int)
modifies hbd;
{   
    var hbd1, hbd2 : [Uid][Pid]int;	
    var hbd3, hbd4 : [Uid][Pid]int;	

    assume(ActiveItem[iid]);

    if (pid == attPid && att)
	{ 			
        hbd1 := hbd[iid];
		hbd[iid]  := hbd2;		
		assume (forall uid:Uid:: hbd[iid][uid][attPid] == lda && hbd[iid][uid][helperPid] == hbd1[uid][helperPid]);	
		ItemRating := Review[iid];				
	}			
	else if ((pid == helperPid) && hb && att)
	{								
		hbd3 := hbd[iid];
		hbd[iid]  := hbd4;
		assume (forall uid:Uid:: hbd[iid][uid][attPid] == hbd3[uid][attPid] && hbd[iid][uid][helperPid] == lda);	
		ItemRating := Review[iid];
	}
	else 
	{
		ItemRating := Review[iid];
	}
}
procedure{:yields}{:layer 1} {:refines "getAllRating"} GetAllRating({:linear "pid"} pid:Pid, iid: Iid) returns (ItemRating: [Uid]int) ;
ensures {:layer 1} ( ActiveItem[iid] ==>  ItemRating == Review[iid] );

///////////////////////////////////////////////////////////////////////////////

// GetAverageRatingByTrustedUser
procedure {:atomic}{:layer 2}  getAverageRatingByTrustedUser(iid:Iid, uid:Uid) returns (ItemTrustedRating : [Uid]int)
{  
    assume(ActiveItem[iid] && ActiveUser[uid]);

    assume(forall uid0:Uid :: Trust[uid][uid0] > 0 ==> ItemTrustedRating[uid0] == Review[iid][uid0]);
}
procedure{:yields}{:layer 1} {:refines "getAverageRatingByTrustedUser"} GetAverageRatingByTrustedUser(iid:Iid,  uid:Uid) returns (ItemTrustedRating: [Uid]int) ;
ensures {:layer 1} ( (ActiveItem[iid] && ActiveUser[uid]) ==> 
                     (forall uid0:Uid :: Trust[uid][uid0] > 0 ==> ItemTrustedRating[uid0] == Review[iid][uid0]) );

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  updateReview({:linear "pid"} pid:Pid, iid:Iid,  {:linear "uid"} uid:Uid, rating: int)
modifies Review;
modifies copyReview;
modifies varAtt1, varAtt2;
modifies att, hb, hbd;
{  
    assume(ActiveItem[iid] && ActiveUser[uid]);

    if (pid == attPid && !att)
	  { 			
		copyReview[iid][uid] := rating;	
		varAtt1 := iid;
		varAtt2 := uid;	
		att := true;				
	  }			

	else if ((pid == helperPid) && !hb && att)
	{								
		assume (hbd[iid][uid][attPid] >= lda);	
		hb := true;				
		hbd[iid][uid][helperPid] := sta;			
		Review[iid][uid] := rating;
	}
	else 
	{
		Review[iid][uid] := rating;
	}
}
procedure{:yields}{:layer 1} {:refines "updateReview"} UpdateReview({:linear "pid"} pid:Pid, iid:Iid,  {:linear "uid"} uid:Uid, rating: int);
ensures {:layer 1} ( (ActiveItem[iid] && ActiveUser[uid]) ==> 
        (Review[iid][uid] == rating) );

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  updateItem(iid:Iid, itName: Itl)
modifies ItemName;
{  
    assume(ActiveItem[iid]);

    ItemName[iid] := itName;
}
procedure{:yields}{:layer 1} {:refines "updateItem"} UpdateItem(iid:Iid, itName: Itl);
ensures {:layer 1} ( ActiveItem[iid] ==> 
        (ItemName[iid] == itName) );

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  updateTrust({:linear "uid"} uidS:Uid, uidT: Uid, trust: int)
modifies Trust;
{  
    assume(ActiveUser[uidS] && ActiveUser[uidT]);

    Trust[uidS][uidT] := trust;
}
procedure{:yields}{:layer 1} {:refines "updateTrust"} UpdateTrust({:linear "uid"} uidS:Uid, uidT: Uid, trust: int);
ensures {:layer 1} ( (ActiveUser[uidS] && ActiveUser[uidT]) ==> 
        (Trust[uidS][uidT] == trust) );

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  updateUser({:linear "uid"} uid:Uid, userName: Unm)
modifies UserName;
{  
    assume(ActiveUser[uid]);

    UserName[uid] := userName;
}
procedure{:yields}{:layer 1} {:refines "updateUser"} UpdateUser({:linear "uid"} uid:Uid, userName: Unm);
ensures {:layer 1} ( ActiveUser[uid] ==> 
        (UserName[uid] == userName) );