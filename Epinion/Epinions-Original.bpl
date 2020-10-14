// Epinions Application
// It has 8 transactions
// A user is represented by a single process
// RUN: /usr/bin/time -v --format="%e" %boogie -noinfer -typeEncoding:m -tracePOs -traceTimes  -trace  -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type Pid;           // Process identifier

type Iid;            // Item identifier
type Uid;          // User identifier

type Unm;          // User Name
type Itl;         // Item Title

function {:builtin "MapConst"} MapConstBool(bool):[Pid]bool;
function {:inline} {:linear "pid"} PidCollector(x: Pid):[Pid]bool
{
  MapConstBool(false)[x := true]
}

function {:builtin "MapConst"} MapConstBool2(bool):[Uid]bool;
function {:inline} {:linear "uid"} UidCollector(x:Uid):[Uid]bool
{
  MapConstBool2(false)[x := true]
}

var {:layer 0,2} ActiveUser: [Uid]bool;
var {:layer 0,2} UserName: [Uid]Unm;

var {:layer 0,2} Review: [Iid][Uid]int;
var {:layer 0,2} Trust: [Uid][Uid]int;

var {:layer 0,2} ActiveItem: [Iid]bool;
var {:layer 0,2} ItemName: [Iid]Itl;

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  getItemReviewsByTrustedUser(iid:Iid, uid:Uid) returns (ItemReviewers:[Uid]int, TrustedUsers:[Uid]int)
{  
    assume(ActiveUser[uid] && ActiveItem[iid]);

    ItemReviewers := Review[iid] ;
    TrustedUsers := Trust[uid] ;
}
procedure{:yields}{:layer 1} {:refines "getItemReviewsByTrustedUser"} GetItemReviewsByTrustedUser(iid:Iid, uid:Uid) returns (ItemReviewers:[Uid]int, TrustedUsers: [Uid]int) ;
ensures {:layer 1} ( (ActiveUser[uid] && ActiveItem[iid]) ==>  (ItemReviewers == Review[iid] && TrustedUsers == Trust[uid]) );

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  getReviewItem(uid:Uid) returns (UserRating:[Iid]int)
{  
    assume(ActiveUser[uid]);

    assume(forall iid:Iid :: UserRating[iid] == Review[iid][uid]);
}
procedure{:yields}{:layer 1} {:refines "getReviewItem"} GetReviewItem(uid:Uid) returns (UserRating:[Iid]int) ;
ensures {:layer 1} ( ActiveUser[uid] ==>  (forall iid:Iid :: UserRating[iid] == Review[iid][uid]) );

////////////////////////////////////////////////////////////////////////////////

//getAverageRating
//getAllRating
procedure {:atomic}{:layer 2}  getAllRating(iid: Iid) returns (ItemRating:[Uid]int)
{  
    assume(ActiveItem[iid]);

    ItemRating := Review[iid];
}
procedure{:yields}{:layer 1} {:refines "getAllRating"} GetAllRating(iid: Iid) returns (ItemRating:[Uid]int) ;
ensures {:layer 1} ( ActiveItem[iid] ==>  ItemRating == Review[iid] );

////////////////////////////////////////////////////////////////////////////////

// GetAverageRatingByTrustedUser
procedure {:atomic}{:layer 2}  getAverageRatingByTrustedUser(iid:Iid, uid:Uid) returns (ItemTrustedRating:[Uid]int)
{  
    assume(ActiveItem[iid] && ActiveUser[uid]);

    assume(forall uid0:Uid :: Trust[uid][uid0] > 0 ==> ItemTrustedRating[uid0] == Review[iid][uid0]);
}
procedure{:yields}{:layer 1} {:refines "getAverageRatingByTrustedUser"} GetAverageRatingByTrustedUser(iid:Iid, uid:Uid) returns (ItemTrustedRating: [Uid]int) ;
ensures {:layer 1} ( (ActiveItem[iid] && ActiveUser[uid]) ==> (forall uid0:Uid :: Trust[uid][uid0] > 0 ==> ItemTrustedRating[uid0] == Review[iid][uid0]) );

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  updateReview(iid:Iid, {:linear "uid"} uid:Uid, rating:int)
modifies Review;
{  
    assume(ActiveItem[iid] && ActiveUser[uid]);

    Review[iid][uid] := rating;
}
procedure{:yields}{:layer 1} {:refines "updateReview"} UpdateReview(iid:Iid, {:linear "uid"} uid:Uid, rating:int);
ensures {:layer 1} ( (ActiveItem[iid] && ActiveUser[uid]) ==> (Review[iid][uid] == rating) );

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  updateItem(iid:Iid, itName: Itl)
modifies ItemName;
{  
    assume(ActiveItem[iid]);

    ItemName[iid] := itName;
}
procedure{:yields}{:layer 1} {:refines "updateItem"} UpdateItem(iid:Iid, itName:Itl);
ensures {:layer 1} ( ActiveItem[iid] ==> (ItemName[iid] == itName) );

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  updateTrust({:linear "uid"} uidS:Uid, uidT:Uid, trust:int)
modifies Trust;
{  
    assume(ActiveUser[uidS] && ActiveUser[uidT]);

    Trust[uidS][uidT] := trust;
}
procedure{:yields}{:layer 1} {:refines "updateTrust"} UpdateTrust({:linear "uid"} uidS:Uid, uidT:Uid, trust:int);
ensures {:layer 1} ( (ActiveUser[uidS] && ActiveUser[uidT]) ==> (Trust[uidS][uidT] == trust) );

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  updateUser({:linear "uid"} uid:Uid, userName:Unm)
modifies UserName;
{  
    assume(ActiveUser[uid]);

    UserName[uid] := userName;
}
procedure{:yields}{:layer 1} {:refines "updateUser"} UpdateUser({:linear "uid"} uid:Uid, userName:Unm);
ensures {:layer 1} ( ActiveUser[uid] ==>  (UserName[uid] == userName) );