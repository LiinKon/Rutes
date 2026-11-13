use std::fs;
use std::path::PathBuf;
use tauri::Manager;

/// Записать файл, путь к которому пользователь выбрал в окне «Сохранить как…».
#[tauri::command]
fn write_file(path: String, data: Vec<u8>) -> Result<(), String> {
    fs::write(&path, data).map_err(|e| e.to_string())
}

/// Резервная копия всей кампании в выбранную папку:
/// «Развилка — кампания.json» (всегда последняя) + копия за день; храним `keep` последних дней.
#[tauri::command]
fn write_backup(
    dir: String,
    latest_name: String,
    daily_name: String,
    contents: String,
    keep: usize,
) -> Result<String, String> {
    let d = PathBuf::from(&dir);
    fs::create_dir_all(&d).map_err(|e| e.to_string())?;
    fs::write(d.join(&latest_name), &contents).map_err(|e| e.to_string())?;
    fs::write(d.join(&daily_name), &contents).map_err(|e| e.to_string())?;
    let prefix = "Развилка — бэкап ";
    let mut dailies: Vec<PathBuf> = fs::read_dir(&d)
        .map_err(|e| e.to_string())?
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .map(|n| n.starts_with(prefix) && n.ends_with(".json"))
                .unwrap_or(false)
        })
        .collect();
    dailies.sort();
    while dailies.len() > keep.max(1) {
        let old = dailies.remove(0);
        let _ = fs::remove_file(old);
    }
    Ok(d.join(&latest_name).to_string_lossy().to_string())
}

#[cfg_attr(mobile, tauri::mobile_entry_point)]
pub fn run() {
    tauri::Builder::default()
        // второй запуск не открывает вторую копию, а поднимает уже открытое окно
        .plugin(tauri_plugin_single_instance::init(|app, _args, _cwd| {
            if let Some(w) = app.get_webview_window("main") {
                let _ = w.unminimize();
                let _ = w.show();
                let _ = w.set_focus();
            }
        }))
        // окно запоминает размер и положение
        .plugin(tauri_plugin_window_state::Builder::default().build())
        .plugin(tauri_plugin_dialog::init())
        .plugin(tauri_plugin_opener::init())
        .invoke_handler(tauri::generate_handler![write_file, write_backup])
        .run(tauri::generate_context!())
        .expect("не удалось запустить Развилку");
}
