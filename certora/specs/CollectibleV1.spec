methods {
  function balanceOf(address) external returns (uint) envfree;
  function ownerOf(uint256 tokenId) external returns (address) envfree;
  function transferable() external returns (bool) envfree;
  function totalSupply() external returns (uint) envfree;
  function maxSupply() external returns (uint) envfree;
  function mintedCount() external returns (uint) envfree;
}



persistent ghost mathint numOfBalanceChanges; 

persistent ghost mathint sumOfBalances /* sigma balanceOF(u) forall u */
{
	init_state axiom sumOfBalances == 0;
}
 

hook Sstore _balances[KEY address addr] uint256 newValue (uint256 oldValue) STORAGE {
    sumOfBalances = sumOfBalances - oldValue + newValue;
    numOfBalanceChanges = numOfBalanceChanges + 1;
}


hook Sload uint256 balance _balances[KEY address addr] STORAGE {
    require sumOfBalances >= to_mathint(balance);
}


invariant totalSupplyIsSumOfBalances() 
    to_mathint(totalSupply()) == sumOfBalances 
    { preserved  {
          requireInvariant maxSupplyVsTotalSupply();
        }
    }


rule atMostTwoUpdates(method f) {
  require numOfBalanceChanges == 0; 
  calldataarg args;
  env e; 
  f(e, args); 
  assert  numOfBalanceChanges <= 2; 
}
rule integrityOfTransfer() {

    address sender;
    address recipient;
    uint256 token_id;
    env e;
    requireInvariant totalSupplyIsSumOfBalances();
    // we still need the following require 
    require balanceOf(sender) + balanceOf(recipient) <= sumOfBalances; 
  
    mathint balance_sender_before = balanceOf(sender);
    mathint balance_recipient_before = balanceOf(recipient);
    transferFrom(e, sender, recipient, token_id);

    assert ownerOf(token_id) == recipient;
    assert sender != recipient => to_mathint(balanceOf(sender)) == balance_sender_before - 1;
    assert sender != recipient => to_mathint(balanceOf(recipient)) == balance_recipient_before + 1; 
    assert sender == recipient => to_mathint(balanceOf(recipient)) == balance_recipient_before; 
}
 
   
rule transferIsPossibleForOwner() {

    address sender;
    address recipient;
    uint256 token_id;
    uint256 token_id2;
    env e;
    require token_id != token_id2; 
    mathint balance_sender_before = balanceOf(sender);
    transferFrom(e, sender, recipient, token_id);
    satisfy balance_sender_before == 2 && ownerOf(token_id2) == sender;
}

rule transferReverts() {
    address sender;
    address recipient;
    uint256 token_id;
    env e;
    mathint balance_sender_before = balanceOf(sender);
    transferFrom@withrevert(e, sender, recipient, token_id);
    bool reverted = lastReverted;
    assert (sender != recipient && balance_sender_before == 0)  => reverted;
}

rule orderOfTransfer() {
    address sender;
    address recipient;
    uint256 token_id;
    address sender2;
    address recipient2;
    uint256 token_id2;

    uint256 token_id3;
    env e;
    env e2;
    require token_id != token_id2; 

    storage init = lastStorage; 

    transferFrom(e, sender, recipient, token_id);
    transferFrom(e2, sender2, recipient2, token_id2);
    address owner = ownerOf(token_id3);

    transferFrom(e2, sender2, recipient2, token_id2) at init;
    transferFrom(e, sender, recipient, token_id);

    assert ownerOf(token_id3)  == owner ;
}





rule changeToMaxSupply(method f) {
  address u;
  uint256 before = maxSupply();
  calldataarg args; env e;
  f(e, args); 
  assert maxSupply() < before => f.selector == sig:setMaxSupply(uint256).selector;
}

 rule sanity(env e, method f) { 
     calldataarg args; 
     f(e, args); 
     satisfy true; 
 } 

invariant balanceOfzero() 
  balanceOf(0) == 0; 

invariant maxSupplyVsTotalSupply() 
  maxSupply() >= mintedCount()  &&  mintedCount() >= totalSupply() ;


/*

this rule require loop unrolling two: 


*/
rule integrityOfMintTo_loop2() {
  address[] addresses;
  env e;

  require addresses.length >= 2;
  mathint supply_before = totalSupply();

  mintTo(e, addresses);

  mathint supply_after = totalSupply();

  assert supply_after == supply_before ;
}



// see this rule with rule_sanity advance and loop iter 1 

rule mintToCanNotMintMoreThanMaxSupply {
  address[] addresses;
  env e;

  mathint totalSupply_before = totalSupply();
  mathint maxSupply = to_mathint(maxSupply());

  require totalSupply_before < maxSupply;

  mintTo@withrevert(e, addresses);
  bool failed = lastReverted;
  assert totalSupply_before + addresses.length > maxSupply => failed ;
}


/// rule mintTo_FromOwner {
///   // address owner;
///   address recipient_1;
///   address recipient_2;
///
///   env e;
///   require recipient_1 != recipient_2;
///   // require e.msg.sender == owner;
///   // require owner() == owner;
///   require maxSupply() == 100000;
///   require totalSupply() == 0;
///   require balanceOf(recipient_1) == 0;
///   require balanceOf(recipient_2) == 0;
///
///   assert balanceOf(recipient_1) == 0, "balance of recipient_1 should be 0";
///   assert balanceOf(recipient_2) == 0, "balance of recipient_2 should be 0";
///
///   mintTo(e, [recipient_1, recipient_2]);
///
///   assert balanceOf(recipient_1) == 1, "balance of recipient_1 should be 1";
///   assert balanceOf(recipient_2) == 1, "balance of recipient_2 should be 1";
/// }
///
/// rule transferNFT_validOwner {
///   address sender;
///   address recipient;
///   uint token_id;
///
///   env e;
///   require e.msg.sender == sender;
///   require sender != recipient;
///   require ownerOf(token_id) == sender;
///   require transferable() == true;
///
///   mathint balance_sender_before = balanceOf(sender);
///   mathint balance_recipient_before = balanceOf(recipient);
///
///   transferFrom(e, sender, recipient, token_id);
///
///   assert ownerOf(token_id) == recipient;
///   assert balanceOf(sender) == assert_uint256(balance_sender_before - 1);
///   /* assert balanceOf(recipient) == balance_recipient_before + 1; */
/// }
///
/// rule transferNFT_invalidOwner {
///   address sender;
///   address recipient;
///   uint token_id;
///
///   env e;
///   require e.msg.sender == sender;
///   require sender != recipient;
///   require ownerOf(token_id) != sender;
///   require transferable() == true;
///
///   transferFrom@withrevert(e, sender, recipient, token_id);
///   assert lastReverted, "transfer should revert when the sender is not the owner of tokenId";
/// }
///
/// rule transferSoulbound {
///   address sender;
///   address recipient;
///   uint token_id;
///
///   env e;
///   require e.msg.sender == sender;
///   require sender != recipient;
///   require ownerOf(token_id) == sender;
///   require transferable() == false;
///
///   mathint balance_sender_before = balanceOf(sender);
///   mathint balance_recipient_before = balanceOf(recipient);
///
///   transferFrom@withrevert(e, sender, recipient, token_id);
///
///   assert lastReverted, "transfer should revert if it's a Soulbound token";
/// }
///
 /* rule wrong(env e, method f) {
   require balanceOf(u)() > totalSupply();

   calldataarg args;
   f(e, args); // call all public/external functions of a contract

   assert mintedCount() < totalSupply();
 } */