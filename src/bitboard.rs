use std::iter;
use std::{fmt, ops};
use std::iter::FusedIterator;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Square(pub u8);

impl fmt::Display for Square {
    fn fmt(&self, fmt : &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let (file, rank) = self.file_rank();
        let actual_rank = ((rank as i8 - 8).abs() as u8 + b'0') as char;

        let _ = fmt.write_str(&format!("{}{}",
                                       (file + b'a') as char,
                                       actual_rank));
        Ok(())
    }
}

impl Square {

    pub fn from_ints (file : u8, rank : u8) -> Self {
        debug_assert!(file < 8 && rank < 8);
        Square((rank << 3) | file)
    }
    pub fn file_rank (self) -> (u8, u8) {
        (self.file(), self.rank())
    }
    pub fn file(self) -> u8 {
        self.0 & 0b0000_0111
    }
    pub fn rank(self) -> u8 {
        self.0 >> 3
    }

    pub const H1 : Square = Square(63);
    pub const G1 : Square = Square(62);
    pub const E1 : Square = Square(60);
    pub const C1 : Square = Square(58);
    pub const A1 : Square = Square(56);

    pub const H8 : Square = Square(7);
    pub const G8 : Square = Square(6);
    pub const E8 : Square = Square(4);
    pub const C8 : Square = Square(2);
    pub const A8 : Square = Square(0);
}


#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct BitBoard {
    pub board: u64,
}

impl ops::BitOr for BitBoard {
    type Output = BitBoard;
    fn bitor(self, rhs: BitBoard) -> BitBoard {
        BitBoard::from_u64(self.board | rhs.board)
    }
}

impl ops::BitOrAssign for BitBoard {
    fn bitor_assign(&mut self, rhs: BitBoard) {
        self.board |= rhs.board
    }
}

impl ops::BitAnd for BitBoard {
    type Output = BitBoard;
    fn bitand(self, rhs: BitBoard) -> BitBoard {
        BitBoard::from_u64(self.board & rhs.board)
    }
}

impl ops::BitAndAssign for BitBoard {
    fn bitand_assign(&mut self, rhs: BitBoard) {
        self.board &= rhs.board
    }
}

impl ops::Not for BitBoard {
    type Output = BitBoard;
    fn not(self) -> BitBoard {
        BitBoard::from_u64(!self.board)
    }
}

impl BitBoard {
    pub const fn empty() -> Self {
        BitBoard { board: 0 }
    }
    pub const fn from_u64(n: u64) -> Self {
        BitBoard { board: n }
    }

    pub const fn get(&self, square: Square) -> bool {
        self.board & (1<<square.0) != 0
    }
    // Sets the square to true
    pub const fn set(self, square: Square) -> Self {
        BitBoard::from_u64(self.board | 1<<square.0)
    }
    #[allow(dead_code)]
    // Sets the square to false
    pub const fn clear(self, square: Square) -> Self {
        BitBoard::from_u64(self.board & !(1<<square.0))
    }

    pub const fn is_empty(&self) -> bool {
        self.board == 0
    }

    pub const fn popcount(&self) -> u32 {
        self.board.count_ones()
    }

    /// Get a single rank
    /// Ranks are numbered from 0 (black's back rank) to 7 (white's back rank)
    pub const fn rank(self, rank: u8) -> u8 {
        (self.board >> (rank * 8)) as u8
    }
    #[allow(dead_code)]
    pub const fn file(self, file: u8) -> u8 {
        self.rotate().rank(file)
    }
    pub const fn rotate(&self) -> Self {
        self.flip_vertical().flip_diagonal()
    }
    pub const fn rotate_270(&self) -> Self {
        self.flip_diagonal().flip_vertical()
    }
    pub const fn rotate_45(&self) -> Self {
        let k1 = 0xAAAAAAAAAAAAAAAA;
        let k2 = 0xCCCCCCCCCCCCCCCC;
        let k4 = 0xF0F0F0F0F0F0F0F0;
        let mut x = self.board;
        x ^= k1 & (x ^ x.rotate_right(8));
        x ^= k2 & (x ^ x.rotate_right(16));
        x ^= k4 & (x ^ x.rotate_right(32));
        Self::from_u64(x)
    }
    pub const fn rotate_315(&self) -> Self {
        let k1 = 0x5555555555555555;
        let k2 = 0x3333333333333333;
        let k4 = 0x0f0f0f0f0f0f0f0f;
        let mut x = self.board;
        x ^= k1 & (x ^ x.rotate_right(8));
        x ^= k2 & (x ^ x.rotate_right(16));
        x ^= k4 & (x ^ x.rotate_right(32));
        Self::from_u64(x)
    }
    #[allow(dead_code)]
    pub const fn flip_horizontal(&self) -> Self {
        let k1 = 0x5555555555555555;
        let k2 = 0x3333333333333333;
        let k4 = 0x0f0f0f0f0f0f0f0f;
        let mut x = self.board;
        x = ((x >> 1) & k1) +  2*(x & k1);
        x = ((x >> 2) & k2) +  4*(x & k2);
        x = ((x >> 4) & k4) + 16*(x & k4);
        BitBoard::from_u64(x)
    }
    pub const fn flip_vertical(&self) -> Self {
        BitBoard::from_u64(self.board.swap_bytes())
    }

    pub const fn flip_diagonal(&self) -> Self {
        let k1 = 0x5500550055005500;
        let k2 = 0x3333000033330000;
        let k4 = 0x0f0f0f0f00000000;
        let mut x = self.board;
        let mut t = k4 & (x ^ (x << 28));
        x ^=       t ^ (t >> 28) ;
        t  = k2 & (x ^ (x << 14));
        x ^=       t ^ (t >> 14) ;
        t  = k1 & (x ^ (x <<  7));
        x ^=       t ^ (t >>  7) ;
        BitBoard::from_u64(x)
    }
    /// Diagonal_id is rank + file
    /// Assumes board is already rotated
    pub fn diagonal(&self, diagonal_id: u8) -> u8 {
        let len = if diagonal_id >= 8 { 15 - diagonal_id } else { diagonal_id + 1 };
        let n = diagonal_id as i8 - 7;
        //let offset = ((7 * n + 8)) % 64;
        let offset = if n <= 0 { n * (-8)} else { 8 * (8 - n) + n };
        ((self.board >> offset) & !(!0 << len)) as u8
    }

    /// Diagonal_id is rank - file
    /// Assumes board is already rotated
    pub fn antidiagonal(&self, diagonal_id: i8) -> u8 {
        let len = 8 - diagonal_id.abs(); // Between 1 and 8
        let n = diagonal_id as i16;
        let offset = if n <= 0 { n * (-8) - n} else { 8 * (8 - n) };
        ((self.board >> offset) & !(!0 << len as u64)) as u8
    }

    pub fn first_piece(&self) -> Option<Square> {
        let square = self.board.trailing_zeros();
        if square == 64 {
            None
        }
        else {
            Some(Square(square as u8))
        }
    }
}

impl fmt::Debug for BitBoard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for n in 0..8 {
            writeln!(f, "{:08b}", (self.board >> (n * 8)) as u8).unwrap();
        }
        Ok(())
    }
}

impl IntoIterator for BitBoard {
    type Item = Square;
    type IntoIter = BitBoardIterator;

    fn into_iter(self) -> Self::IntoIter {
        BitBoardIterator::new(self)
    }
}

impl iter::FromIterator<Square> for BitBoard {
    fn from_iter<T: IntoIterator<Item=Square>>(iter: T) -> Self {
        let mut board = Self::empty();
        for square in iter {
            board = board.set(square);
        }
        board
    }
}

pub struct BitBoardIterator {
    board: BitBoard,
}

impl BitBoardIterator {
    const fn new(board: BitBoard) -> Self {
        Self { board }
    }
}

impl Iterator for BitBoardIterator {
    type Item = Square;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.board.first_piece() {
            self.board = self.board.clear(next);
            Some(next)
        }
        else {
            None
        }
    }
}

impl FusedIterator for BitBoardIterator {}