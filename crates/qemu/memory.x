# Minimal memory map for a LM3S6965EVB.
MEMORY
{
  FLASH : ORIGIN = 0x00000000, LENGTH = 256K
  RAM   : ORIGIN = 0x20000000, LENGTH = 64K
}
PROVIDE(PendSV = PendSV_Handler);
PROVIDE(SysTick = _tx_timer_interrupt);
