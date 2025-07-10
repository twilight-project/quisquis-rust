//! Address utilities for the Quisquis protocol.
//!
//! Provides types and functions for handling network-specific addresses, including
//! serialization, deserialization, and encoding/decoding in various formats.

use sha3::{Digest, Keccak256};
use std::fmt;

use crate::{keys::PublicKey, ristretto::RistrettoPublicKey};
use curve25519_dalek::ristretto::CompressedRistretto;

/// The list of the existing Twilight networks.
///
/// Network type: Mainnet, Testnet.
/// Network implements [`Default`] and returns [`Network::Mainnet`].
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Network {
    /// Mainnet is the "production" network and blockchain.
    Mainnet,
    /// Testnet is the "experimental" network and blockchain where things get released long before
    /// mainnet.
    Testnet,
}

impl Network {
    /// Get the associated magic byte given an address type.
    ///
    /// The byte values should be taken from the blockchain config file. The same values should be used here.
    /// Sample values are used here.
    pub fn as_u8(self, addr_type: &AddressType) -> u8 {
        use AddressType::*;
        match self {
            Network::Mainnet => match addr_type {
                Standard => 12,
                Contract => 24,
            },
            Network::Testnet => match addr_type {
                Standard => 44,
                Contract => 66,
            },
        }
    }

    /// Recover the network type given an address magic byte.
    ///
    /// The byte values should be taken from the blockchain config file. The same values should be used here.
    /// Sample values are used here.
    ///
    /// # Errors
    ///
    /// Returns an error if the byte does not correspond to a known network.
    pub fn from_u8(byte: u8) -> Result<Network, &'static str> {
        use Network::*;
        match byte {
            12 | 24 => Ok(Mainnet),
            44 | 66 => Ok(Testnet),
            _ => Err("Error::InvalidNteworkByte"),
        }
    }
}
/// Default network is Mainnet.
impl Default for Network {
    /// Returns the default network, which is Mainnet.
    fn default() -> Network {
        Network::Mainnet
    }
}

/// Address type: standard, contract.
///
/// AddressType implements [`Default`] and returns [`AddressType::Standard`].
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum AddressType {
    /// Standard twilight account address.
    Standard,
    /// Contract addresses.
    Contract,
}

impl AddressType {
    /// Recover the address type given an address bytes and the network.
    ///
    /// # Errors
    ///
    /// Returns an error if the magic byte does not correspond to a known address type.
    pub fn from_slice(bytes: &[u8], net: Network) -> Result<AddressType, &'static str> {
        let byte = bytes[0];
        use AddressType::*;
        use Network::*;
        match net {
            Mainnet => match byte {
                12 => Ok(Standard),
                24 => Ok(Contract),
                _ => Err("Error::InvalidAddressTypeMagicByte"),
            },
            Testnet => match byte {
                44 => Ok(Standard),
                66 => Ok(Contract),
                _ => Err("Error::InvalidAddressTypeMagicByte"),
            },
        }
    }
}
/// Default address type is Standard.
impl Default for AddressType {
    /// Returns the default address type, which is Standard.
    fn default() -> AddressType {
        AddressType::Standard
    }
}
/// Display the address type.
impl fmt::Display for AddressType {
    /// Formats the address type as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AddressType::Standard => write!(f, "Standard address"),
            AddressType::Contract => write!(f, "Contract"),
        }
    }
}

/// A complete twilight typed address valid for a specific network.
///
/// Contains the network, address type, and the associated public key.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct Address {
    /// The network on which the address is valid and should be used.
    pub network: Network,
    /// The address type.
    pub addr_type: AddressType,
    /// The address public key.
    pub public_key: RistrettoPublicKey,
}

impl Address {
    /// Create a standard address which is valid on the given network.
    ///
    /// # Arguments
    ///
    /// * `network` - The network on which the address is valid and should be used.
    /// * `public_key` - The public key associated with the address.
    ///
    /// # Returns
    ///
    /// A new `Address` instance with the specified network and public key.
    pub fn standard(network: Network, public_key: RistrettoPublicKey) -> Address {
        Address {
            network,
            addr_type: AddressType::Standard,
            public_key,
        }
    }

    /// Create a Contract address which is valid on the given network.
    ///
    /// # Arguments
    ///
    /// * `network` - The network on which the address is valid and should be used.
    /// * `public_key` - The public key associated with the address.
    ///
    /// # Returns
    /// A new `Address` instance with the specified network and public key.
    pub fn contract(network: Network, public_key: RistrettoPublicKey) -> Address {
        Address {
            network,
            addr_type: AddressType::Contract,
            public_key,
        }
    }

    /// Parse an address from a vector of bytes.
    /// 
    /// The input bytes are expected to be in the following format:
    /// [magic byte, public key, checksum]
    /// 
    /// The magic byte is used to determine the network and address type.
    /// The public key is the public key of the address.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The bytes of the address.
    ///
    /// # Returns
    ///
    /// A new `Address` instance with the specified network and public key.
    ///
    /// # Errors
    ///
    /// Returns an error if the magic byte is incorrect, if public keys are not valid points,
    /// or if checksums mismatch.
    pub fn from_bytes(bytes: &[u8]) -> Result<Address, &'static str> {
        let network = Network::from_u8(bytes[0])?;
        let addr_type = AddressType::from_slice(&bytes, network)?;
        let gr = slice_to_pkpoint(&bytes[1..33])?;
        let grsk = slice_to_pkpoint(&bytes[33..65])?;
        let public_key = RistrettoPublicKey { gr, grsk };
        let (checksum_bytes, checksum) = (&bytes[0..65], &bytes[65..69]);
        let mut hasher = Keccak256::new();
        hasher.update(checksum_bytes);
        let checksum_verify = hasher.finalize();
        if &checksum_verify[0..4] != checksum {
            return Err("Invalid Checksum");
        }

        Ok(Address {
            network,
            addr_type,
            public_key,
        })
    }

    /// Serialize the address as a vector of bytes.
    ///
    /// # Returns
    ///
    /// A vector of bytes representing the address.
    /// Byte Format: [magic byte, public key, checksum]
    pub fn as_bytes(&self) -> Vec<u8> {
        let mut bytes = vec![self.network.as_u8(&self.addr_type)];
        bytes.extend_from_slice(self.public_key.as_bytes().as_slice());
        let mut hasher = Keccak256::new();
        hasher.update(&bytes);
        let checksum = hasher.finalize();
        bytes.extend_from_slice(&checksum[0..4]);
        bytes
    }

    /// Serialize the address bytes as a hexadecimal string.
    ///
    /// # Returns
    ///
    /// A hexadecimal string representing the address.
    pub fn as_hex(&self) -> String {
        hex::encode(self.as_bytes())
    }

    /// Serialize the address bytes as a BTC-Base58 string.
    ///
    /// # Returns
    ///
    /// A Base58 string representing the address.
    pub fn as_base58(&self) -> String {
        bs58::encode(self.as_bytes()).into_string()
    }

    /// Convert Hex address string to Address.
    ///
    /// # Panics
    ///
    /// Panics if the hex string is invalid or the address cannot be parsed.
    ///
    /// # Arguments
    ///
    /// * `s` - The hexadecimal string to parse.
    ///
    /// # Returns   
    ///
    /// A new `Address` instance with the specified network and public key.
    pub fn from_hex(s: &str) -> Self {
        Self::from_bytes(&hex::decode(s).unwrap().as_slice()).unwrap()
    }

    /// Convert Base58 address string to Address.
    ///
    /// # Panics
    ///
    /// Panics if the base58 string is invalid or the address cannot be parsed.
    ///
    /// # Arguments
    ///
    /// * `s` - The base58 string to parse.
    ///
    /// # Returns
    ///
    /// A new `Address` instance with the specified network and public key.
    pub fn from_base58(s: &str) -> Self {
        let decoded = bs58::decode(s).into_vec().unwrap();
        Self::from_bytes(&decoded).unwrap()
    }
}

/// Utility function for deserializing a public key from a slice.
///
/// The input slice is 32 bytes.
/// Returns an error if the key is not the correct length or is not a valid point.
fn slice_to_pkpoint(data: &[u8]) -> Result<CompressedRistretto, &'static str> {
    if data.len() != 32 {
        return Err("Invalid Key Length");
    }
    let gr = CompressedRistretto::from_slice(&data);
    match gr.decompress() {
        Some(_) => (),
        None => {
            return Err("InvalidPoint");
        }
    };
    Ok(gr)
}
// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------
#[cfg(test)]
mod test {
    // use super::*;
    #[test]
    fn hex_encoding_decoding_test() {}
}
