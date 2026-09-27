package unlegit.zkm;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;
import javax.swing.UIManager;
import javax.swing.WindowConstants;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.io.File;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * Swing front-end for {@link ZkmFullDeobfuscator}. No arguments opens the GUI.
 * CLI arguments are forwarded to the existing pipeline.
 */
public final class ZkmDeobfuscatorApp {
    private ZkmDeobfuscatorApp() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length == 0) {
            SwingUtilities.invokeLater(new Runnable() {
                @Override
                public void run() {
                    installLookAndFeel();
                    new Window().show();
                }
            });
            return;
        }
        ZkmFullDeobfuscator.main(args);
    }

    private static void installLookAndFeel() {
        try {
            UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
        } catch (Exception ignored) {
        }
    }

    private static final class Window {
        private final JFrame frame = new JFrame("ZKM 27 Full Deobfuscator");
        private final JTextField inputField = new JTextField();
        private final JTextField outputField = new JTextField();
        private final JTextField reportField = new JTextField();
        private final JTextField changelogField = new JTextField();
        private final JTextField authorityField = new JTextField();
        private final JTextField evidenceField = new JTextField();
        private final JCheckBox changelogBox = new JCheckBox("Use changelog (restores original names)", true);
        private final JTextArea log = new JTextArea();
        private final JProgressBar progress = new JProgressBar();
        private final JButton runButton = new JButton("Deobfuscate");
        private SwingWorker<Void, String> worker;

        void show() {
            frame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
            frame.setMinimumSize(new Dimension(780, 620));
            frame.setLayout(new BorderLayout(0, 0));
            frame.add(buildHeader(), BorderLayout.NORTH);
            frame.add(buildForm(), BorderLayout.CENTER);
            frame.add(buildFooter(), BorderLayout.SOUTH);
            frame.pack();
            frame.setLocationRelativeTo(null);
            frame.setVisible(true);
        }

        private JPanel buildHeader() {
            JPanel header = new JPanel(new BorderLayout());
            header.setBorder(BorderFactory.createEmptyBorder(16, 18, 8, 18));
            JLabel title = new JLabel("ZKM 27 Full Deobfuscator");
            title.setFont(title.getFont().deriveFont(Font.BOLD, 20f));
            JLabel subtitle = new JLabel("Static ASM undo for Zelix KlassMaster 27. Input classes are never loaded.");
            subtitle.setForeground(new Color(80, 80, 80));
            header.add(title, BorderLayout.NORTH);
            header.add(subtitle, BorderLayout.SOUTH);
            return header;
        }

        private JPanel buildForm() {
            JPanel form = new JPanel(new GridBagLayout());
            form.setBorder(BorderFactory.createEmptyBorder(4, 18, 8, 18));
            GridBagConstraints c = new GridBagConstraints();
            c.insets = new Insets(4, 0, 4, 8);
            c.fill = GridBagConstraints.HORIZONTAL;
            c.weightx = 1;
            int row = 0;
            row = addPathRow(form, c, row, "Input JAR", inputField, true, "Choose the ZKM-obfuscated archive");
            row = addPathRow(form, c, row, "Output JAR", outputField, true, "Where to write the deobfuscated archive");
            row = addPathRow(form, c, row, "Report directory", reportField, false, "TSV / audit output (optional)");
            c.gridx = 0;
            c.gridy = row++;
            c.gridwidth = 3;
            form.add(changelogBox, c);
            c.gridwidth = 1;
            row = addPathRow(form, c, row, "Changelog", changelogField, true, "Optional ZKM changeLogFileOut");
            row = addPathRow(form, c, row, "Runtime authority", authorityField, true, "Optional pre-removal authority JAR");
            row = addPathRow(form, c, row, "Semantic overrides", evidenceField, true, "Optional evidence TSV");
            changelogBox.addActionListener(e -> changelogField.setEnabled(changelogBox.isSelected()));

            log.setEditable(false);
            log.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
            log.setLineWrap(true);
            log.setWrapStyleWord(true);
            JScrollPane scroll = new JScrollPane(log);
            scroll.setPreferredSize(new Dimension(720, 240));
            scroll.setBorder(BorderFactory.createTitledBorder("Log"));
            c.gridx = 0;
            c.gridy = row;
            c.gridwidth = 3;
            c.weighty = 1;
            c.fill = GridBagConstraints.BOTH;
            form.add(scroll, c);
            return form;
        }

        private int addPathRow(JPanel form, GridBagConstraints c, int row, String label,
                               JTextField field, boolean files, String browseTitle) {
            JLabel name = new JLabel(label);
            JButton browse = new JButton("Browse");
            browse.addActionListener(e -> choose(field, files, browseTitle));
            c.gridy = row;
            c.weighty = 0;
            c.fill = GridBagConstraints.HORIZONTAL;
            c.gridx = 0;
            c.weightx = 0;
            c.gridwidth = 1;
            form.add(name, c);
            c.gridx = 1;
            c.weightx = 1;
            form.add(field, c);
            c.gridx = 2;
            c.weightx = 0;
            form.add(browse, c);
            return row + 1;
        }

        private JPanel buildFooter() {
            JPanel footer = new JPanel(new BorderLayout(8, 0));
            footer.setBorder(BorderFactory.createEmptyBorder(0, 18, 16, 18));
            progress.setIndeterminate(false);
            progress.setStringPainted(true);
            progress.setString("Idle");
            JPanel buttons = new JPanel(new FlowLayout(FlowLayout.RIGHT, 8, 0));
            JButton quit = new JButton("Quit");
            quit.addActionListener(e -> System.exit(0));
            runButton.addActionListener(e -> start());
            buttons.add(quit);
            buttons.add(runButton);
            footer.add(progress, BorderLayout.CENTER);
            footer.add(buttons, BorderLayout.EAST);
            return footer;
        }

        private void choose(JTextField field, boolean files, String title) {
            JFileChooser chooser = new JFileChooser();
            chooser.setDialogTitle(title);
            if (files) {
                chooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
                chooser.setFileFilter(new FileNameExtensionFilter(
                        "Archives and text", "jar", "zip", "txt", "tsv"));
            } else {
                chooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
            }
            String current = field.getText().trim();
            if (!current.isEmpty()) {
                File existing = new File(current);
                chooser.setCurrentDirectory(existing.isDirectory()
                        ? existing : existing.getParentFile());
            }
            if (chooser.showOpenDialog(frame) == JFileChooser.APPROVE_OPTION) {
                field.setText(chooser.getSelectedFile().getAbsolutePath());
                suggestDefaults();
            }
        }

        private void suggestDefaults() {
            String input = inputField.getText().trim();
            if (input.isEmpty()) return;
            File in = new File(input);
            if (outputField.getText().trim().isEmpty() && in.getParentFile() != null) {
                String name = in.getName();
                int dot = name.lastIndexOf('.');
                String stem = dot < 0 ? name : name.substring(0, dot);
                outputField.setText(new File(in.getParentFile(), stem + "-deobf.jar").getAbsolutePath());
            }
            if (reportField.getText().trim().isEmpty() && in.getParentFile() != null) {
                reportField.setText(new File(in.getParentFile(), "zkm-deobf-report").getAbsolutePath());
            }
        }

        private void start() {
            if (worker != null && !worker.isDone()) return;
            final File input = new File(inputField.getText().trim());
            final File output = new File(outputField.getText().trim());
            String reportText = reportField.getText().trim();
            final File report = new File(reportText.isEmpty()
                    ? new File(output.getParentFile() == null ? new File(".") : output.getParentFile(),
                    "zkm-deobf-report").getAbsolutePath()
                    : reportText);
            final File changelog = changelogBox.isSelected() && !changelogField.getText().trim().isEmpty()
                    ? new File(changelogField.getText().trim()) : null;
            final File authority = emptyToNull(authorityField);
            final File evidence = emptyToNull(evidenceField);
            if (!input.isFile()) {
                JOptionPane.showMessageDialog(frame, "Choose an existing input JAR.",
                        "Missing input", JOptionPane.WARNING_MESSAGE);
                return;
            }
            if (outputField.getText().trim().isEmpty()) {
                JOptionPane.showMessageDialog(frame, "Choose an output JAR path.",
                        "Missing output", JOptionPane.WARNING_MESSAGE);
                return;
            }
            if (input.getAbsolutePath().equals(output.getAbsolutePath())) {
                JOptionPane.showMessageDialog(frame, "Output must not replace the input JAR.",
                        "Unsafe output", JOptionPane.WARNING_MESSAGE);
                return;
            }
            log.setText("");
            runButton.setEnabled(false);
            progress.setIndeterminate(true);
            progress.setString("Running");
            worker = new SwingWorker<Void, String>() {
                @Override
                protected Void doInBackground() {
                    PrintStream originalOut = System.out;
                    PrintStream originalErr = System.err;
                    PrintStream capture = new PrintStream(new LogStream(), true);
                    System.setOut(capture);
                    System.setErr(capture);
                    try {
                        publish("input=" + input.getAbsolutePath());
                        publish("output=" + output.getAbsolutePath());
                        publish("report=" + report.getAbsolutePath());
                        if (changelog != null) publish("changelog=" + changelog.getAbsolutePath());
                        Files.createDirectories(report.toPath());
                        Path parent = output.toPath().toAbsolutePath().getParent();
                        if (parent != null) Files.createDirectories(parent);
                        List<String> args = new ArrayList<String>();
                        args.add(input.getAbsolutePath());
                        args.add(report.getAbsolutePath());
                        args.add(output.getAbsolutePath());
                        if (changelog != null) {
                            args.add("--changelog");
                            args.add(changelog.getAbsolutePath());
                        }
                        if (authority != null) {
                            args.add("--runtime-authority");
                            args.add(authority.getAbsolutePath());
                        }
                        if (evidence != null) {
                            args.add("--runtime-semantic-overrides");
                            args.add(evidence.getAbsolutePath());
                        }
                        ZkmFullDeobfuscator.main(args.toArray(new String[0]));
                        publish("done");
                    } catch (Throwable failure) {
                        publish("ERROR " + failure.getClass().getSimpleName() + ": "
                                + String.valueOf(failure.getMessage()));
                    } finally {
                        System.setOut(originalOut);
                        System.setErr(originalErr);
                    }
                    return null;
                }

                @Override
                protected void process(List<String> chunks) {
                    for (String chunk : chunks) {
                        log.append(chunk);
                        if (!chunk.endsWith("\n")) log.append("\n");
                    }
                    log.setCaretPosition(log.getDocument().getLength());
                }

                @Override
                protected void done() {
                    runButton.setEnabled(true);
                    progress.setIndeterminate(false);
                    progress.setString("Idle");
                }
            };
            worker.execute();
        }

        private File emptyToNull(JTextField field) {
            String text = field.getText().trim();
            return text.isEmpty() ? null : new File(text);
        }

        private final class LogStream extends OutputStream {
            private final StringBuilder buffer = new StringBuilder();

            @Override
            public void write(int b) {
                if (b == '\n') {
                    flushLine();
                } else if (b != '\r') {
                    buffer.append((char) b);
                }
            }

            @Override
            public void write(byte[] bytes, int off, int len) {
                String text = new String(bytes, off, len, StandardCharsets.UTF_8);
                for (int i = 0; i < text.length(); i++) {
                    char ch = text.charAt(i);
                    if (ch == '\n') flushLine();
                    else if (ch != '\r') buffer.append(ch);
                }
            }

            private void flushLine() {
                final String line = buffer.toString();
                buffer.setLength(0);
                SwingUtilities.invokeLater(new Runnable() {
                    @Override
                    public void run() {
                        log.append(line);
                        log.append("\n");
                        log.setCaretPosition(log.getDocument().getLength());
                    }
                });
            }
        }
    }
}
