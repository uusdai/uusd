// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "@openzeppelin/contracts/proxy/transparent/TransparentUpgradeableProxy.sol";
import "@openzeppelin/contracts/proxy/transparent/ProxyAdmin.sol";
import "../src/UUSD.sol";

contract UUSDTest is Test {
    UUSD public implementation;
    UUSD public uusd;
    ProxyAdmin public proxyAdmin;
    TransparentUpgradeableProxy public proxy;

    address public owner;
    address public admin = address(0x2);
    address public minter = address(0x3);
    address public user1 = address(0x4);
    address public user2 = address(0x5);

    function setUp() public {
        // Use this test contract as owner initially
        owner = address(this);

        // Deploy implementation
        implementation = new UUSD();

        // Deploy ProxyAdmin
        proxyAdmin = new ProxyAdmin(owner);

        // Deploy proxy
        bytes memory initData = abi.encodeWithSelector(
            UUSD.initialize.selector,
            "Unity USD",
            "UUSD",
            owner
        );
        proxy = new TransparentUpgradeableProxy(
            address(implementation),
            address(proxyAdmin),
            initData
        );

        // Get UUSD interface
        uusd = UUSD(address(proxy));
    }

    // ============ Basic Token Tests ============

    function test_Name() public view {
        assertEq(uusd.name(), "Unity USD");
    }

    function test_Symbol() public view {
        assertEq(uusd.symbol(), "UUSD");
    }

    function test_Decimals() public view {
        assertEq(uusd.decimals(), 18);
    }

    function test_InitialSupply() public view {
        assertEq(uusd.totalSupply(), 0);
    }

    function test_Owner() public view {
        assertEq(uusd.owner(), owner);
    }

    // ============ Owner Mint/Burn Tests ============

    function test_OwnerMint() public {
        uusd.mint(1000 ether);
        assertEq(uusd.balanceOf(owner), 1000 ether);
    }

    function test_OwnerMintTo() public {
        uusd.mintTo(user1, 500 ether);
        assertEq(uusd.balanceOf(user1), 500 ether);
    }

    function test_OwnerBurn() public {
        uusd.mint(1000 ether);
        uusd.burn(400 ether);
        assertEq(uusd.balanceOf(owner), 600 ether);
    }

    function test_RevertMintNotOwner() public {
        vm.prank(user1);
        vm.expectRevert();
        uusd.mint(100 ether);
    }

    // ============ Admin Tests ============

    function test_SetAdmin() public {
        uusd.setAdmin(admin);
        assertEq(uusd.admin(), admin);
    }

    function test_AdminFreeze() public {
        uusd.setAdmin(admin);

        vm.prank(admin);
        uusd.freeze(user1);
        assertTrue(uusd.frozen(user1));
    }

    function test_AdminPause() public {
        uusd.setAdmin(admin);

        vm.prank(admin);
        uusd.pause();
        assertTrue(uusd.paused());
    }

    function test_OwnerCanAlsoFreeze() public {
        uusd.freeze(user1);
        assertTrue(uusd.frozen(user1));
    }

    function test_NonAdminCannotFreeze() public {
        vm.prank(user1);
        vm.expectRevert(UUSD.NotAdminOrOwner.selector);
        uusd.freeze(user2);
    }

    // ============ Minter Tests ============

    function test_AddMinter() public {
        uusd.addMinter(minter);
        assertTrue(uusd.isMinter(minter));
    }

    function test_MinterMint() public {
        uusd.addMinter(minter);
        uusd.setMinterAllowance(minter, 1000 ether);

        vm.prank(minter);
        uusd.minterMint(user1, 500 ether);

        assertEq(uusd.balanceOf(user1), 500 ether);
        assertEq(uusd.minterAllowance(minter), 500 ether);
    }

    function test_MinterBurn() public {
        uusd.addMinter(minter);
        uusd.setMinterAllowance(minter, 1000 ether);

        vm.startPrank(minter);
        uusd.minterMint(minter, 500 ether);
        uusd.minterBurn(200 ether);
        vm.stopPrank();

        assertEq(uusd.balanceOf(minter), 300 ether);
    }

    function test_MinterAllowanceExceeded() public {
        uusd.addMinter(minter);
        uusd.setMinterAllowance(minter, 100 ether);

        vm.prank(minter);
        vm.expectRevert(abi.encodeWithSelector(UUSD.MinterAllowanceExceeded.selector, 200 ether, 100 ether));
        uusd.minterMint(user1, 200 ether);
    }

    function test_RemoveMinter() public {
        uusd.addMinter(minter);
        uusd.setMinterAllowance(minter, 1000 ether);
        uusd.removeMinter(minter);

        assertFalse(uusd.isMinter(minter));
        assertEq(uusd.minterAllowance(minter), 0);
    }

    function test_NonMinterCannotMint() public {
        vm.prank(user1);
        vm.expectRevert(UUSD.NotMinter.selector);
        uusd.minterMint(user2, 100 ether);
    }

    function test_FrozenMinterCannotMint() public {
        // Setup minter
        uusd.addMinter(minter);
        uusd.setMinterAllowance(minter, 1000 ether);

        // Freeze the minter
        uusd.freeze(minter);

        // Frozen minter cannot mint
        vm.prank(minter);
        vm.expectRevert(abi.encodeWithSelector(UUSD.AccountFrozen.selector, minter));
        uusd.minterMint(user1, 100 ether);
    }

    function test_FrozenMinterCannotBurn() public {
        // Setup minter with some tokens
        uusd.addMinter(minter);
        uusd.setMinterAllowance(minter, 1000 ether);

        vm.prank(minter);
        uusd.minterMint(minter, 500 ether);

        // Freeze the minter
        uusd.freeze(minter);

        // Frozen minter cannot burn
        vm.prank(minter);
        vm.expectRevert(abi.encodeWithSelector(UUSD.AccountFrozen.selector, minter));
        uusd.minterBurn(100 ether);
    }

    // ============ Freeze Tests ============

    function test_FrozenCannotTransfer() public {
        uusd.mintTo(user1, 100 ether);
        uusd.freeze(user1);

        vm.prank(user1);
        vm.expectRevert(abi.encodeWithSelector(UUSD.AccountFrozen.selector, user1));
        uusd.transfer(user2, 50 ether);
    }

    function test_CannotTransferToFrozen() public {
        uusd.mintTo(user1, 100 ether);
        uusd.freeze(user2);

        vm.prank(user1);
        vm.expectRevert(abi.encodeWithSelector(UUSD.AccountFrozen.selector, user2));
        uusd.transfer(user2, 50 ether);
    }

    function test_CannotMintToFrozen() public {
        uusd.freeze(user1);

        vm.expectRevert(abi.encodeWithSelector(UUSD.AccountFrozen.selector, user1));
        uusd.mintTo(user1, 100 ether);
    }

    function test_Unfreeze() public {
        uusd.mintTo(user1, 100 ether);
        uusd.freeze(user1);
        uusd.unfreeze(user1);

        vm.prank(user1);
        uusd.transfer(user2, 50 ether);
        assertEq(uusd.balanceOf(user2), 50 ether);
    }

    function test_FrozenSpenderCannotTransferFrom() public {
        // Setup: user1 has tokens and approves user2 (spender)
        uusd.mintTo(user1, 100 ether);

        vm.prank(user1);
        uusd.approve(user2, 50 ether);

        // Verify allowance is set
        assertEq(uusd.allowance(user1, user2), 50 ether);

        // Freeze the spender (user2)
        uusd.freeze(user2);

        // Frozen spender should NOT be able to use their existing allowance
        vm.prank(user2);
        vm.expectRevert(abi.encodeWithSelector(UUSD.AccountFrozen.selector, user2));
        uusd.transferFrom(user1, address(0x999), 25 ether);
    }

    function test_UnfrozenSpenderCanTransferFrom() public {
        // Setup: user1 has tokens and approves user2 (spender)
        uusd.mintTo(user1, 100 ether);

        vm.prank(user1);
        uusd.approve(user2, 50 ether);

        // Freeze then unfreeze the spender
        uusd.freeze(user2);
        uusd.unfreeze(user2);

        // Unfrozen spender should be able to use their allowance
        vm.prank(user2);
        uusd.transferFrom(user1, address(0x999), 25 ether);

        assertEq(uusd.balanceOf(address(0x999)), 25 ether);
        assertEq(uusd.allowance(user1, user2), 25 ether);
    }

    // ============ Pause Tests ============

    function test_PausedCannotTransfer() public {
        uusd.mintTo(user1, 100 ether);
        uusd.pause();

        vm.prank(user1);
        vm.expectRevert();
        uusd.transfer(user2, 50 ether);
    }

    function test_Unpause() public {
        uusd.mintTo(user1, 100 ether);
        uusd.pause();
        uusd.unpause();

        vm.prank(user1);
        uusd.transfer(user2, 50 ether);
        assertEq(uusd.balanceOf(user2), 50 ether);
    }

    // ============ Batch Transfer Tests ============

    function test_BatchTransfer() public {
        uusd.mintTo(user1, 1000 ether);

        address[] memory recipients = new address[](3);
        recipients[0] = address(0x10);
        recipients[1] = address(0x11);
        recipients[2] = address(0x12);

        uint256[] memory amounts = new uint256[](3);
        amounts[0] = 100 ether;
        amounts[1] = 200 ether;
        amounts[2] = 300 ether;

        vm.prank(user1);
        uusd.batchTransfer(recipients, amounts);

        assertEq(uusd.balanceOf(address(0x10)), 100 ether);
        assertEq(uusd.balanceOf(address(0x11)), 200 ether);
        assertEq(uusd.balanceOf(address(0x12)), 300 ether);
        assertEq(uusd.balanceOf(user1), 400 ether);
    }

    function test_BatchTransferSizeLimit() public {
        uusd.mintTo(user1, 100000 ether);

        address[] memory recipients = new address[](201);
        uint256[] memory amounts = new uint256[](201);
        for (uint256 i = 0; i < 201; i++) {
            recipients[i] = address(uint160(0x100 + i));
            amounts[i] = 1 ether;
        }

        vm.prank(user1);
        vm.expectRevert(abi.encodeWithSelector(UUSD.BatchSizeExceeded.selector, 201, 200));
        uusd.batchTransfer(recipients, amounts);
    }

    function test_BatchTransferLengthMismatch() public {
        uusd.mintTo(user1, 100 ether);

        address[] memory recipients = new address[](2);
        recipients[0] = address(0x10);
        recipients[1] = address(0x11);

        uint256[] memory amounts = new uint256[](3);
        amounts[0] = 10 ether;
        amounts[1] = 20 ether;
        amounts[2] = 30 ether;

        vm.prank(user1);
        vm.expectRevert(UUSD.BatchLengthMismatch.selector);
        uusd.batchTransfer(recipients, amounts);
    }

    // ============ Ownership Tests ============

    function test_RenounceOwnershipDisabled() public {
        vm.expectRevert(UUSD.RenounceOwnershipDisabled.selector);
        uusd.renounceOwnership();
    }

    function test_TwoStepOwnershipTransfer() public {
        address newOwner = address(0x999);

        uusd.transferOwnership(newOwner);

        // Still owner until accepted
        assertEq(uusd.owner(), owner);

        vm.prank(newOwner);
        uusd.acceptOwnership();

        assertEq(uusd.owner(), newOwner);
    }

    // ============ EIP-2612 Permit Tests ============

    function test_Permit() public {
        uint256 privateKey = 0x1234;
        address signer = vm.addr(privateKey);

        uusd.mintTo(signer, 100 ether);

        uint256 deadline = block.timestamp + 1 hours;
        uint256 nonce = uusd.nonces(signer);

        bytes32 permitHash = keccak256(
            abi.encodePacked(
                "\x19\x01",
                uusd.DOMAIN_SEPARATOR(),
                keccak256(
                    abi.encode(
                        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"),
                        signer,
                        user1,
                        50 ether,
                        nonce,
                        deadline
                    )
                )
            )
        );

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(privateKey, permitHash);

        uusd.permit(signer, user1, 50 ether, deadline, v, r, s);

        assertEq(uusd.allowance(signer, user1), 50 ether);
    }

    // ============ EIP-3009 Tests ============

    function test_TransferWithAuthorization() public {
        uint256 privateKey = 0x1234;
        address signer = vm.addr(privateKey);

        uusd.mintTo(signer, 100 ether);

        uint256 validAfter = block.timestamp - 1;
        uint256 validBefore = block.timestamp + 1 hours;
        bytes32 nonce = bytes32(uint256(1));

        bytes32 structHash = keccak256(
            abi.encode(
                uusd.TRANSFER_WITH_AUTHORIZATION_TYPEHASH(),
                signer,
                user1,
                50 ether,
                validAfter,
                validBefore,
                nonce
            )
        );

        bytes32 digest = keccak256(
            abi.encodePacked("\x19\x01", uusd.DOMAIN_SEPARATOR(), structHash)
        );

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(privateKey, digest);

        vm.prank(user2); // Anyone can submit
        uusd.transferWithAuthorization(signer, user1, 50 ether, validAfter, validBefore, nonce, v, r, s);

        assertEq(uusd.balanceOf(user1), 50 ether);
        assertEq(uusd.balanceOf(signer), 50 ether);
    }

    function test_ReceiveWithAuthorization() public {
        uint256 privateKey = 0x1234;
        address signer = vm.addr(privateKey);

        uusd.mintTo(signer, 100 ether);

        uint256 validAfter = block.timestamp - 1;
        uint256 validBefore = block.timestamp + 1 hours;
        bytes32 nonce = bytes32(uint256(2));

        bytes32 structHash = keccak256(
            abi.encode(
                uusd.RECEIVE_WITH_AUTHORIZATION_TYPEHASH(),
                signer,
                user1,
                30 ether,
                validAfter,
                validBefore,
                nonce
            )
        );

        bytes32 digest = keccak256(
            abi.encodePacked("\x19\x01", uusd.DOMAIN_SEPARATOR(), structHash)
        );

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(privateKey, digest);

        vm.prank(user1); // Receiver must be caller
        uusd.receiveWithAuthorization(signer, user1, 30 ether, validAfter, validBefore, nonce, v, r, s);

        assertEq(uusd.balanceOf(user1), 30 ether);
    }

    function test_TransferWithAuthorizationExactValidAfterFails() public {
        // EIP-3009: valid window is (validAfter, validBefore) - open interval
        // When block.timestamp == validAfter, authorization is NOT yet valid
        uint256 privateKey = 0x1234;
        address signer = vm.addr(privateKey);

        uusd.mintTo(signer, 100 ether);

        uint256 validAfter = block.timestamp; // Exact boundary - should fail
        uint256 validBefore = block.timestamp + 1 hours;
        bytes32 nonce = bytes32(uint256(99));

        bytes32 structHash = keccak256(
            abi.encode(
                uusd.TRANSFER_WITH_AUTHORIZATION_TYPEHASH(),
                signer,
                user1,
                10 ether,
                validAfter,
                validBefore,
                nonce
            )
        );

        bytes32 digest = keccak256(
            abi.encodePacked("\x19\x01", uusd.DOMAIN_SEPARATOR(), structHash)
        );

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(privateKey, digest);

        // Should FAIL when block.timestamp == validAfter (per EIP-3009)
        vm.expectRevert(UUSD.AuthorizationNotYetValid.selector);
        uusd.transferWithAuthorization(signer, user1, 10 ether, validAfter, validBefore, nonce, v, r, s);
    }

    function test_CancelAuthorization() public {
        uint256 privateKey = 0x1234;
        address signer = vm.addr(privateKey);

        bytes32 nonce = bytes32(uint256(3));

        bytes32 structHash = keccak256(
            abi.encode(
                uusd.CANCEL_AUTHORIZATION_TYPEHASH(),
                signer,
                nonce
            )
        );

        bytes32 digest = keccak256(
            abi.encodePacked("\x19\x01", uusd.DOMAIN_SEPARATOR(), structHash)
        );

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(privateKey, digest);

        uusd.cancelAuthorization(signer, nonce, v, r, s);

        assertTrue(uusd.authorizationState(signer, nonce));
    }
}
