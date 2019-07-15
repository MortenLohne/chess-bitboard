use crate::bitboard::BitBoard;
use crate::bitboard::Square;

const CHESS_START_BOARD: BitBoard = BitBoard::from_u64(0xFFFF_0000_0000_FFFF);

#[test]
fn pext_test() {
    let board = BitBoard::from_u64(255 << 8);
    assert_eq!(board.extract_pieces(BitBoard::full()), board);
    assert!(board.extract_pieces(BitBoard::empty()).is_empty());

    assert_eq!(
        board.extract_pieces(BitBoard::from_u64(1023 ^ 255)),
        BitBoard::from_u64(3)
    );
    assert_eq!(
        board.extract_pieces(BitBoard::from_u64(1023)),
        BitBoard::from_u64(512 + 256)
    );
}

#[test]
fn pdep_test() {
    let board = BitBoard::from_u64(255 << 8);
    assert_eq!(board.deposit_pieces(BitBoard::full()), board);
    assert!(board.deposit_pieces(BitBoard::empty()).is_empty());

    assert_eq!(
        board.deposit_pieces(BitBoard::from_u64(1023)),
        BitBoard::from_u64(512 + 256)
    );
}

#[test]
fn rotate() {
    let empty = BitBoard::empty();
    assert_eq!(empty, empty.rotate());

    let mut board = CHESS_START_BOARD;

    assert_eq!(board, board.rotate().rotate());

    assert_eq!(board, board.rotate().rotate().rotate().rotate());

    board = board.rotate();
    for rank in 0..8 {
        for &file in [0, 1, 6, 7].iter() {
            assert!(board.get(Square::from_ints(file, rank)));
        }
        for &file in [2, 3, 4, 5].iter() {
            assert!(
                !board.get(Square::from_ints(file, rank)),
                "Found piece in the middle of board \n{:?}",
                board
            );
        }
    }
}

use quickcheck::Arbitrary;
use quickcheck::Gen;

impl Arbitrary for BitBoard {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        BitBoard::from_u64(g.next_u64())
    }
}

impl Arbitrary for Square {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        Square((g.next_u64() % 64) as u8)
    }
}

quickcheck! {
    fn rotation_45_preserves_pieces(bitboard: BitBoard) -> bool {
        bitboard.rotate_45().board.count_ones() == bitboard.board.count_ones()
    }

    fn diagonals_preserve_pieces(bitboard: BitBoard) -> bool {
        (0..15).map(|n| bitboard.diagonal(n)).map(u8::count_ones).sum::<u32>() == bitboard.popcount()
    }

    fn rotation_315_preserves_pieces(bitboard: BitBoard) -> bool {
        bitboard.rotate_315().board.count_ones() == bitboard.board.count_ones()
    }

    fn antidiagonals_preserve_pieces(bitboard: BitBoard) -> bool {
        (-7..8).map(|n| bitboard.antidiagonal(n))
            .map(u8::count_ones)
            .sum::<u32>() == bitboard.popcount()
    }

    fn rotate_315_back(bitboard: BitBoard) -> bool {
        (0..8).fold(bitboard, |board, _| board.rotate_315()) == bitboard
    }

    fn rotate_45_back(bitboard: BitBoard) -> bool {
        (0..8).fold(bitboard, |board, _| board.rotate_45()) == bitboard
    }

    fn iterator_iterates_all(bitboard: BitBoard) -> bool {
        bitboard.into_iter().count() == bitboard.popcount() as usize
    }

    fn iterator(bitboard: BitBoard) -> bool {
        let mut board = BitBoard::empty();
        for square in bitboard {
            board = board.set(square);
        }
        board == bitboard
    }

    fn from_to_iterator(bitboard: BitBoard) -> bool {
        bitboard.into_iter().collect::<BitBoard>() == bitboard
    }

    fn pext_quickcheck(board1: BitBoard, board2: BitBoard) -> bool {
        (board1 & board2).popcount() == board1.extract_pieces(board2).popcount()
    }

    fn pdep_quickcheck(board1: BitBoard, board2: BitBoard) -> bool {
        let bits_to_deposit = board2.popcount();
        let lower_n_bits = 2_u64.pow(bits_to_deposit) - 1;
        (BitBoard::from_u64(lower_n_bits) & board1).popcount() == board1.deposit_pieces(board2).popcount()
    }

    fn pext_pdep_quickcheck(board1: BitBoard, board2: BitBoard) -> bool {
        let extracted = board1.extract_pieces(board2);
        let deposited = extracted.deposit_pieces(board2);
        (board1 & (!board2)) | (board1 & (deposited)) == board1
    }
}

#[test]
fn rotate_45() {
    let board = CHESS_START_BOARD;
    let board2 = (0..8).fold(board, |b, _| b.rotate_45());
    assert_eq!(board, board2);
}

#[test]
fn long_diagonal() {
    let board = CHESS_START_BOARD.rotate_45();
    assert_eq!(
        board.diagonal(7),
        0b1100_0011,
        "\nDiagonal: {:b}\n{:?}",
        board.diagonal(7),
        BitBoard::from_u64(board.board)
    );
    assert_eq!(
        board.diagonal(8),
        0b0100_0011,
        "\nDiagonal: {:b}\n{:?}",
        board.diagonal(8),
        BitBoard::from_u64(board.board)
    );
    assert_eq!(board.diagonal(9), 0b11, "\n{:?}", board);
    assert_eq!(board.diagonal(13), 0b11, "\n{:?}", board);
    assert_eq!(board.diagonal(14), 1);
    assert_eq!(board.diagonal(0), 1);
    assert_eq!(board.diagonal(1), 0b11);
    assert_eq!(board.diagonal(2), 0b110);
}

#[test]
fn long_antidiagonal() {
    let board = CHESS_START_BOARD.rotate_315();
    assert_eq!(
        board.antidiagonal(0),
        0b1100_0011,
        "\nDiagonal: {:b}\n{:?}",
        board.antidiagonal(0),
        BitBoard::from_u64(board.board)
    );
    assert_eq!(
        board.antidiagonal(1),
        0b0110_0001,
        "\nDiagonal: {:b}\n{:?}",
        board.antidiagonal(1),
        board
    );
    assert_eq!(board.antidiagonal(2), 0b11_0000, "\n{:?}", board);
    assert_eq!(board.antidiagonal(6), 0b11, "\n{:?}", board);
    assert_eq!(board.antidiagonal(7), 1);
    assert_eq!(board.antidiagonal(-7), 1);
    assert_eq!(board.antidiagonal(-6), 0b11);
    assert_eq!(board.antidiagonal(-5), 0b011);
}
