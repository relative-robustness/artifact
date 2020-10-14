// Epinions Application
// It has 8 transactions
// A user is represented by a single process
// Movers check
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

procedure {:atomic}{:layer 2} getItemReviewsByTrustedUser(iid:Iid, uid:Uid) 
            returns (ItemReviewers:[Uid]int, TrustedUsers:[Uid]int)
{  
    assume(ActiveUser[uid] && ActiveItem[iid]);

    ItemReviewers := Review[iid] ;
    TrustedUsers := Trust[uid] ;
}
procedure{:yields}{:layer 1} {:refines "getItemReviewsByTrustedUser"} GetItemReviewsByTrustedUser(iid:Iid, uid:Uid) 
            returns (ItemReviewers:[Uid]int, TrustedUsers: [Uid]int);

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  getReviewItem(uid:Uid) returns (UserRating:[Iid]int)
{  
    assume(ActiveUser[uid]);

    assume(forall iid:Iid :: UserRating[iid] == Review[iid][uid]);
}
procedure{:yields}{:layer 1} {:refines "getReviewItem"} GetReviewItem(uid:Uid) returns (UserRating:[Iid]int);

////////////////////////////////////////////////////////////////////////////////

//getAverageRating
//getAllRating
procedure {:atomic}{:layer 2}  getAllRating(iid: Iid) returns (ItemRating:[Uid]int)
{  
    assume(ActiveItem[iid]);

    ItemRating := Review[iid];
}
procedure{:yields}{:layer 1} {:refines "getAllRating"} GetAllRating(iid: Iid) returns (ItemRating: [Uid]int);

////////////////////////////////////////////////////////////////////////////////

// GetAverageRatingByTrustedUser
procedure {:atomic}{:layer 2}  getAverageRatingByTrustedUser(iid:Iid, uid:Uid) returns (ItemTrustedRating:[Uid]int)
{  
    assume(ActiveItem[iid] && ActiveUser[uid]);

    assume(forall uid0:Uid :: Trust[uid][uid0] > 0 ==> ItemTrustedRating[uid0] == Review[iid][uid0]);
}
procedure{:yields}{:layer 1} {:refines "getAverageRatingByTrustedUser"} GetAverageRatingByTrustedUser(iid:Iid, uid:Uid) 
            returns (ItemTrustedRating:[Uid]int);
           
////////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2}  updateReviewR(iid:Iid, {:linear "uid"} uid:Uid, rating: int)
{  
    assume(ActiveItem[iid] && ActiveUser[uid]);
}
procedure{:yields}{:layer 1} {:refines "updateReviewR"} UpdateReviewR(iid:Iid, {:linear "uid"} uid:Uid, rating:int);

////////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2}  updateReviewW(iid:Iid, {:linear "uid"} uid:Uid, rating: int)
modifies Review;
{  
    Review[iid][uid] := rating;
}
procedure{:yields}{:layer 1} {:refines "updateReviewW"} UpdateReviewW(iid:Iid, {:linear "uid"} uid:Uid, rating:int);

////////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2}  updateItemR(iid:Iid, itName: Itl)
{  
    assume(ActiveItem[iid]);
}
procedure{:yields}{:layer 1} {:refines "updateItemR"} UpdateItemR(iid:Iid, itName:Itl);

////////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2}  updateItemW(iid:Iid, itName: Itl)
modifies ItemName;
{  
    ItemName[iid] := itName;
}
procedure{:yields}{:layer 1} {:refines "updateItemW"} UpdateItemW(iid:Iid, itName: Itl);
ensures {:layer 1} ( ActiveItem[iid] ==> 
        (ItemName[iid] == itName) );

////////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2}  updateTrustR({:linear "uid"} uidS:Uid, uidT:Uid, trust: int)
{  
    assume(ActiveUser[uidS] && ActiveUser[uidT]);
}
procedure{:yields}{:layer 1} {:refines "updateTrustR"} UpdateTrustR({:linear "uid"} uidS:Uid, uidT:Uid, trust:int);

////////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2}  updateTrustW({:linear "uid"} uidS:Uid, uidT:Uid, trust: int)
modifies Trust;
{  
    Trust[uidS][uidT] := trust;
}
procedure{:yields}{:layer 1} {:refines "updateTrustW"} UpdateTrustW({:linear "uid"} uidS:Uid, uidT:Uid, trust:int);

////////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2}  updateUserR({:linear "uid"} uid:Uid, userName:Unm)
{  
    assume(ActiveUser[uid]);
}
procedure{:yields}{:layer 1} {:refines "updateUserR"} UpdateUserR({:linear "uid"} uid:Uid, userName:Unm);

////////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2}  updateUserW({:linear "uid"} uid:Uid, userName:Unm)
modifies UserName;
{  
    UserName[uid] := userName;
}
procedure{:yields}{:layer 1} {:refines "updateUserW"} UpdateUserW({:linear "uid"} uid:Uid, userName:Unm);