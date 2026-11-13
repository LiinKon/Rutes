// В релизной сборке на Windows не показываем лишнее окно консоли.
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

fn main() {
    razvilka_lib::run()
}
