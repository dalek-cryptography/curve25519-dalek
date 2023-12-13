use utralib::generated::*;
pub struct Uart {
    // pub base: *mut u32,
}

impl Uart {
    fn put_digit(&mut self, d: u8) {
        let nyb = d & 0xF;
        if nyb < 10 {
            self.putc(nyb + 0x30);
        } else {
            self.putc(nyb + 0x61 - 10);
        }
    }
    pub fn put_hex(&mut self, c: u8) {
        self.put_digit(c >> 4);
        self.put_digit(c & 0xF);
    }
    pub fn newline(&mut self) {
        self.putc(0xa);
        self.putc(0xd);
    }
    pub fn print_hex_word(&mut self, word: u32) {
        for &byte in word.to_be_bytes().iter() {
            self.put_hex(byte);
        }
    }

    pub fn putc(&self, c: u8) {
        let base = utra::uart::HW_UART_BASE as *mut u32;
        let mut uart = CSR::new(base);
        // Wait until TXFULL is `0`
        while uart.r(utra::uart::TXFULL) != 0 {}
        uart.wo(utra::uart::RXTX, c as u32)
    }

    pub fn getc(&self) -> Option<u8> {
        let base = utra::uart::HW_UART_BASE as *mut u32;
        let mut uart = CSR::new(base);
        match uart.rf(utra::uart::EV_PENDING_RX) {
            0 => None,
            ack => {
                let c = Some(uart.rf(utra::uart::RXTX_RXTX) as u8);
                uart.wfo(utra::uart::EV_PENDING_RX, ack);
                c
            }
        }
    }

    pub fn tiny_write_str(&mut self, s: &str) {
        for c in s.bytes() {
            self.putc(c);
        }
    }

}

use core::fmt::{Error, Write};
impl Write for Uart {
    fn write_str(&mut self, s: &str) -> Result<(), Error> {
        for c in s.bytes() {
            self.putc(c);
        }
        Ok(())
    }
}

#[macro_use]
pub mod debug_print_hardware {
    #[macro_export]
    macro_rules! print
    {
        ($($args:tt)+) => ({
                use core::fmt::Write;
                let _ = write!(debug::Uart {}, $($args)+);
        });
    }
}

#[macro_use]
#[cfg(test)]
mod debug_print_hardware {
    #[macro_export]
    #[allow(unused_variables)]
    macro_rules! print {
        ($($args:tt)+) => ({
            std::print!($($args)+)
        });
    }
}

#[macro_export]
macro_rules! println
{
    () => ({
        $crate::print!("\r\n")
    });
    ($fmt:expr) => ({
        $crate::print!(concat!($fmt, "\r\n"))
    });
    ($fmt:expr, $($args:tt)+) => ({
        $crate::print!(concat!($fmt, "\r\n"), $($args)+)
    });
}
