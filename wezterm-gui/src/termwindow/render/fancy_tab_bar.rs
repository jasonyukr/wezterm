use crate::customglyph::*;
use crate::tabbar::{parse_status_text, TabBarItem, TabEntry};
use crate::termwindow::box_model::*;
use crate::termwindow::render::corners::*;

use crate::termwindow::render::window_buttons::window_button_element;
use crate::termwindow::{UIItem, UIItemType};
use crate::utilsprites::RenderMetrics;
use config::{Dimension, DimensionContext, TabBarColors};
use std::rc::Rc;
use termwiz::cell::CellAttributes;
use wezterm_font::LoadedFont;
use wezterm_term::color::{ColorAttribute, ColorPalette};
use window::{IntegratedTitleButtonAlignment, IntegratedTitleButtonStyle};

const X_BUTTON: &[Poly] = &[
    Poly {
        path: &[
            PolyCommand::MoveTo(BlockCoord::One, BlockCoord::Zero),
            PolyCommand::LineTo(BlockCoord::Zero, BlockCoord::One),
        ],
        intensity: BlockAlpha::Full,
        style: PolyStyle::Outline,
    },
    Poly {
        path: &[
            PolyCommand::MoveTo(BlockCoord::Zero, BlockCoord::Zero),
            PolyCommand::LineTo(BlockCoord::One, BlockCoord::One),
        ],
        intensity: BlockAlpha::Full,
        style: PolyStyle::Outline,
    },
];

const PLUS_BUTTON: &[Poly] = &[
    Poly {
        path: &[
            PolyCommand::MoveTo(BlockCoord::Frac(1, 2), BlockCoord::Zero),
            PolyCommand::LineTo(BlockCoord::Frac(1, 2), BlockCoord::One),
        ],
        intensity: BlockAlpha::Full,
        style: PolyStyle::Outline,
    },
    Poly {
        path: &[
            PolyCommand::MoveTo(BlockCoord::Zero, BlockCoord::Frac(1, 2)),
            PolyCommand::LineTo(BlockCoord::One, BlockCoord::Frac(1, 2)),
        ],
        intensity: BlockAlpha::Full,
        style: PolyStyle::Outline,
    },
];

impl crate::TermWindow {
    pub fn invalidate_fancy_tab_bar(&mut self) {
        self.fancy_tab_bar.take();
    }

    /// The padding at the left of the tab strip; it varies with the window
    /// decorations because the integrated window buttons live there.
    fn fancy_tab_bar_left_padding(&self) -> Dimension {
        let window_buttons_at_left = self
            .config
            .window_decorations
            .contains(window::WindowDecorations::INTEGRATED_BUTTONS)
            && (self.config.integrated_title_button_alignment
                == IntegratedTitleButtonAlignment::Left
                || self.config.integrated_title_button_style
                    == IntegratedTitleButtonStyle::MacOsNative);

        if window_buttons_at_left {
            if self.config.integrated_title_button_style == IntegratedTitleButtonStyle::MacOsNative
            {
                if !self.window_state.contains(window::WindowState::FULL_SCREEN) {
                    Dimension::Pixels(70.0)
                } else {
                    Dimension::Cells(0.5)
                }
            } else {
                Dimension::Pixels(0.0)
            }
        } else {
            Dimension::Cells(0.5)
        }
    }

    fn fancy_tab_bar_geometry(
        &self,
        font: &Rc<LoadedFont>,
        metrics: &RenderMetrics,
    ) -> FancyTabBarGeometry {
        let cell_width = metrics.cell_size.width as f32;
        let cell_height = metrics.cell_size.height as f32;

        FancyTabBarGeometry {
            cell_width,
            cell_height,
            text_cell_width: measure_cell_width(font, metrics),
            pixel_width: self.dimensions.pixel_width as f32,
            left_padding: self
                .fancy_tab_bar_left_padding()
                .evaluate_as_pixels(DimensionContext {
                    dpi: self.dimensions.dpi as f32,
                    pixel_max: self.dimensions.pixel_width as f32,
                    pixel_cell: cell_width,
                }),
            close_button: if self.config.show_close_tab_button_in_tabs {
                (cell_height / 2.) + cell_width
            } else {
                0.
            },
            tab_max_width: self.config.tab_max_width,
        }
    }

    /// How many cells of title text a tab in the fancy tab bar can show.
    ///
    /// The tab bar model clamps the titles - and tells `format-tab-title` how
    /// much room it has - in cells, but the fancy tab bar lays the tabs out in
    /// pixels, so it is the only thing that knows how much room there really
    /// is. Returns None when the fancy tab bar is not in use.
    pub fn fancy_tab_bar_title_cells(&self, num_tabs: usize) -> Option<usize> {
        if !self.config.use_fancy_tab_bar {
            return None;
        }

        let font = self.fonts.title_font().ok()?;
        let metrics = RenderMetrics::with_font_metrics(&font.metrics());
        let geometry = self.fancy_tab_bar_geometry(&font, &metrics);

        let status_cells = parse_status_text(&self.left_status, CellAttributes::default()).len()
            + parse_status_text(&self.right_status, CellAttributes::default()).len();

        let window_buttons = if self
            .config
            .window_decorations
            .contains(window::WindowDecorations::INTEGRATED_BUTTONS)
            && self.config.integrated_title_button_style != IntegratedTitleButtonStyle::MacOsNative
        {
            self.config.integrated_title_buttons.len()
        } else {
            0
        };

        Some(geometry.title_cells(
            num_tabs,
            geometry.reserved(
                self.config.show_new_tab_button_in_tab_bar,
                status_cells,
                window_buttons,
            ),
        ))
    }

    pub fn build_fancy_tab_bar(&self, palette: &ColorPalette) -> anyhow::Result<ComputedElement> {
        let tab_bar_height = self.tab_bar_pixel_height()?;
        let font = self.fonts.title_font()?;
        let metrics = RenderMetrics::with_font_metrics(&font.metrics());
        let items = self.tab_bar.items();
        let colors = self
            .config
            .colors
            .as_ref()
            .and_then(|c| c.tab_bar.as_ref())
            .cloned()
            .unwrap_or_else(TabBarColors::default);

        let mut left_status = vec![];
        let mut left_eles = vec![];
        let mut right_eles = vec![];
        let bar_colors = ElementColors {
            border: BorderColor::default(),
            bg: if self.focused.is_some() {
                self.config.window_frame.active_titlebar_bg
            } else {
                self.config.window_frame.inactive_titlebar_bg
            }
            .to_linear()
            .into(),
            text: if self.focused.is_some() {
                self.config.window_frame.active_titlebar_fg
            } else {
                self.config.window_frame.inactive_titlebar_fg
            }
            .to_linear()
            .into(),
        };

        let item_to_elem = |item: &TabEntry| -> Element {
            let element = Element::with_line(&font, &item.title, palette);

            let bg_color = item
                .title
                .get_cell(0)
                .and_then(|c| match c.attrs().background() {
                    ColorAttribute::Default => None,
                    col => Some(palette.resolve_bg(col)),
                });
            let fg_color = item
                .title
                .get_cell(0)
                .and_then(|c| match c.attrs().foreground() {
                    ColorAttribute::Default => None,
                    col => Some(palette.resolve_fg(col)),
                });

            let new_tab = colors.new_tab();
            let new_tab_hover = colors.new_tab_hover();
            let active_tab = colors.active_tab();

            match item.item {
                TabBarItem::RightStatus | TabBarItem::LeftStatus | TabBarItem::None => element
                    .item_type(UIItemType::TabBar(TabBarItem::None))
                    .line_height(Some(1.75))
                    .margin(BoxDimension {
                        left: Dimension::Cells(0.),
                        right: Dimension::Cells(0.),
                        top: Dimension::Cells(0.0),
                        bottom: Dimension::Cells(0.),
                    })
                    .padding(BoxDimension {
                        left: Dimension::Cells(0.5),
                        right: Dimension::Cells(0.),
                        top: Dimension::Cells(0.),
                        bottom: Dimension::Cells(0.),
                    })
                    .border(BoxDimension::new(Dimension::Pixels(0.)))
                    .colors(bar_colors.clone()),
                TabBarItem::NewTabButton => Element::new(
                    &font,
                    ElementContent::Poly {
                        line_width: metrics.underline_height.max(2),
                        poly: SizedPoly {
                            poly: PLUS_BUTTON,
                            width: Dimension::Pixels(metrics.cell_size.height as f32 / 2.),
                            height: Dimension::Pixels(metrics.cell_size.height as f32 / 2.),
                        },
                    },
                )
                .vertical_align(VerticalAlign::Middle)
                .item_type(UIItemType::TabBar(item.item.clone()))
                .margin(BoxDimension {
                    left: Dimension::Cells(0.5),
                    right: Dimension::Cells(0.),
                    top: Dimension::Cells(0.2),
                    bottom: Dimension::Cells(0.),
                })
                .padding(BoxDimension {
                    left: Dimension::Cells(0.5),
                    right: Dimension::Cells(0.5),
                    top: Dimension::Cells(0.2),
                    bottom: Dimension::Cells(0.25),
                })
                .border(BoxDimension::new(Dimension::Pixels(1.)))
                .colors(ElementColors {
                    border: BorderColor::default(),
                    bg: new_tab.bg_color.to_linear().into(),
                    text: new_tab.fg_color.to_linear().into(),
                })
                .hover_colors(Some(ElementColors {
                    border: BorderColor::default(),
                    bg: new_tab_hover.bg_color.to_linear().into(),
                    text: new_tab_hover.fg_color.to_linear().into(),
                })),
                TabBarItem::Tab { active, .. } if active => element
                    .vertical_align(VerticalAlign::Bottom)
                    .item_type(UIItemType::TabBar(item.item.clone()))
                    .margin(BoxDimension {
                        left: Dimension::Cells(0.),
                        right: Dimension::Cells(0.),
                        top: Dimension::Cells(0.2),
                        bottom: Dimension::Cells(0.),
                    })
                    .padding(BoxDimension {
                        left: Dimension::Cells(0.5),
                        right: Dimension::Cells(0.5),
                        top: Dimension::Cells(0.2),
                        bottom: Dimension::Cells(0.25),
                    })
                    .border(BoxDimension::new(Dimension::Pixels(1.)))
                    .border_corners(Some(Corners {
                        top_left: SizedPoly {
                            width: Dimension::Cells(0.5),
                            height: Dimension::Cells(0.5),
                            poly: TOP_LEFT_ROUNDED_CORNER,
                        },
                        top_right: SizedPoly {
                            width: Dimension::Cells(0.5),
                            height: Dimension::Cells(0.5),
                            poly: TOP_RIGHT_ROUNDED_CORNER,
                        },
                        bottom_left: SizedPoly::none(),
                        bottom_right: SizedPoly::none(),
                    }))
                    .colors(ElementColors {
                        border: BorderColor::new(
                            bg_color
                                .unwrap_or_else(|| active_tab.bg_color.into())
                                .to_linear(),
                        ),
                        bg: bg_color
                            .unwrap_or_else(|| active_tab.bg_color.into())
                            .to_linear()
                            .into(),
                        text: fg_color
                            .unwrap_or_else(|| active_tab.fg_color.into())
                            .to_linear()
                            .into(),
                    }),
                TabBarItem::Tab { .. } => element
                    .vertical_align(VerticalAlign::Bottom)
                    .item_type(UIItemType::TabBar(item.item.clone()))
                    .margin(BoxDimension {
                        left: Dimension::Cells(0.),
                        right: Dimension::Cells(0.),
                        top: Dimension::Cells(0.2),
                        bottom: Dimension::Cells(0.),
                    })
                    .padding(BoxDimension {
                        left: Dimension::Cells(0.5),
                        right: Dimension::Cells(0.5),
                        top: Dimension::Cells(0.2),
                        bottom: Dimension::Cells(0.25),
                    })
                    .border(BoxDimension::new(Dimension::Pixels(1.)))
                    .border_corners(Some(Corners {
                        top_left: SizedPoly {
                            width: Dimension::Cells(0.5),
                            height: Dimension::Cells(0.5),
                            poly: TOP_LEFT_ROUNDED_CORNER,
                        },
                        top_right: SizedPoly {
                            width: Dimension::Cells(0.5),
                            height: Dimension::Cells(0.5),
                            poly: TOP_RIGHT_ROUNDED_CORNER,
                        },
                        bottom_left: SizedPoly {
                            width: Dimension::Cells(0.),
                            height: Dimension::Cells(0.33),
                            poly: &[],
                        },
                        bottom_right: SizedPoly {
                            width: Dimension::Cells(0.),
                            height: Dimension::Cells(0.33),
                            poly: &[],
                        },
                    }))
                    .colors({
                        let inactive_tab = colors.inactive_tab();
                        let bg = bg_color
                            .unwrap_or_else(|| inactive_tab.bg_color.into())
                            .to_linear();
                        let edge = colors.inactive_tab_edge().to_linear();
                        ElementColors {
                            border: BorderColor {
                                left: bg,
                                right: edge,
                                top: bg,
                                bottom: bg,
                            },
                            bg: bg.into(),
                            text: fg_color
                                .unwrap_or_else(|| inactive_tab.fg_color.into())
                                .to_linear()
                                .into(),
                        }
                    })
                    .hover_colors({
                        let inactive_tab_hover = colors.inactive_tab_hover();
                        Some(ElementColors {
                            border: BorderColor::new(
                                bg_color
                                    .unwrap_or_else(|| inactive_tab_hover.bg_color.into())
                                    .to_linear(),
                            ),
                            bg: bg_color
                                .unwrap_or_else(|| inactive_tab_hover.bg_color.into())
                                .to_linear()
                                .into(),
                            text: fg_color
                                .unwrap_or_else(|| inactive_tab_hover.fg_color.into())
                                .to_linear()
                                .into(),
                        })
                    }),
                TabBarItem::WindowButton(button) => window_button_element(
                    button,
                    self.window_state.contains(window::WindowState::MAXIMIZED),
                    &font,
                    &metrics,
                    &self.config,
                ),
            }
        };

        // Sharing the window width evenly between every tab *and* the new tab
        // button shrinks the titles as soon as a tab is added and leaves the
        // right hand end of the tab bar unused. Instead, work out what the
        // non-tab furniture actually costs and give the tabs the rest.
        let cell_width = metrics.cell_size.width as f32;
        let geometry = self.fancy_tab_bar_geometry(&font, &metrics);

        let mut tab_count = 0;
        let mut status_cells = 0;
        let mut window_buttons = 0;
        let mut new_tab_button = false;
        for item in items {
            match item.item {
                TabBarItem::Tab { .. } => tab_count += 1,
                TabBarItem::NewTabButton => new_tab_button = true,
                TabBarItem::WindowButton(_) => window_buttons += 1,
                _ => status_cells += item.title.len(),
            }
        }

        let reserved = geometry.reserved(new_tab_button, status_cells, window_buttons);
        let max_tab_width = geometry.tab_width(tab_count, reserved);
        // The title is clipped here so that it stops short of the close
        // button rather than running underneath it.
        let max_title_width = geometry.title_width(tab_count, reserved);

        // Reserve space for the native titlebar buttons
        if self
            .config
            .window_decorations
            .contains(::window::WindowDecorations::INTEGRATED_BUTTONS)
            && self.config.integrated_title_button_style == IntegratedTitleButtonStyle::MacOsNative
            && !self.window_state.contains(window::WindowState::FULL_SCREEN)
        {
            left_status.push(
                Element::new(&font, ElementContent::Text("".to_string())).margin(BoxDimension {
                    left: Dimension::Cells(4.0), // FIXME: determine exact width of macos ... buttons
                    right: Dimension::Cells(0.),
                    top: Dimension::Cells(0.),
                    bottom: Dimension::Cells(0.),
                }),
            );
        }

        for item in items {
            match item.item {
                TabBarItem::LeftStatus => left_status.push(item_to_elem(item)),
                TabBarItem::None | TabBarItem::RightStatus => right_eles.push(item_to_elem(item)),
                TabBarItem::WindowButton(_) => {
                    if self.config.integrated_title_button_alignment
                        == IntegratedTitleButtonAlignment::Left
                    {
                        left_eles.push(item_to_elem(item))
                    } else {
                        right_eles.push(item_to_elem(item))
                    }
                }
                TabBarItem::Tab { tab_idx, active } => {
                    let mut elem = item_to_elem(item);
                    elem.max_width = Some(Dimension::Pixels(max_tab_width));
                    // An element is sized to its content and text only renders
                    // in whole cells, so without a matching minimum each tab
                    // rounds down to a cell boundary and the remainders add up
                    // to a gap at the right hand end of the bar. min_width is
                    // measured in content space, so take off the 0.5 cells of
                    // padding either side and the 1px border either side.
                    elem.min_width =
                        Some(Dimension::Pixels((max_tab_width - cell_width - 2.).max(0.)));
                    elem.content = match elem.content {
                        ElementContent::Text(_) => unreachable!(),
                        ElementContent::Poly { .. } => unreachable!(),
                        ElementContent::Children(kids) => {
                            // The close button floats at the right hand end of
                            // the tab, so the title has to be bounded in its
                            // own right; left to itself it is laid out across
                            // the whole of the tab and the button is then
                            // drawn on top of its last cell.
                            let mut kids =
                                vec![Element::new(&font, ElementContent::Children(kids))
                                    .max_width(Some(Dimension::Pixels(max_title_width)))];
                            if self.config.show_close_tab_button_in_tabs {
                                kids.push(make_x_button(&font, &metrics, &colors, tab_idx, active));
                            }
                            ElementContent::Children(kids)
                        }
                    };
                    left_eles.push(elem);
                }
                _ => left_eles.push(item_to_elem(item)),
            }
        }

        let mut children = vec![];

        if !left_status.is_empty() {
            children.push(
                Element::new(&font, ElementContent::Children(left_status))
                    .colors(bar_colors.clone()),
            );
        }

        let left_padding = self.fancy_tab_bar_left_padding();

        children.push(
            Element::new(&font, ElementContent::Children(left_eles))
                .vertical_align(VerticalAlign::Bottom)
                .colors(bar_colors.clone())
                .padding(BoxDimension {
                    left: left_padding,
                    right: Dimension::Cells(0.),
                    top: Dimension::Cells(0.),
                    bottom: Dimension::Cells(0.),
                })
                .zindex(1),
        );
        children.push(
            Element::new(&font, ElementContent::Children(right_eles))
                .colors(bar_colors.clone())
                .float(Float::Right),
        );

        let content = ElementContent::Children(children);

        let tabs = Element::new(&font, content)
            .display(DisplayType::Block)
            .item_type(UIItemType::TabBar(TabBarItem::None))
            .min_width(Some(Dimension::Pixels(self.dimensions.pixel_width as f32)))
            .min_height(Some(Dimension::Pixels(tab_bar_height)))
            .vertical_align(VerticalAlign::Bottom)
            .colors(bar_colors);

        let border = self.get_os_border();

        let mut computed = self.compute_element(
            &LayoutContext {
                height: DimensionContext {
                    dpi: self.dimensions.dpi as f32,
                    pixel_max: self.dimensions.pixel_height as f32,
                    pixel_cell: metrics.cell_size.height as f32,
                },
                width: DimensionContext {
                    dpi: self.dimensions.dpi as f32,
                    pixel_max: self.dimensions.pixel_width as f32,
                    pixel_cell: metrics.cell_size.width as f32,
                },
                bounds: euclid::rect(
                    border.left.get() as f32,
                    0.,
                    self.dimensions.pixel_width as f32 - (border.left + border.right).get() as f32,
                    tab_bar_height,
                ),
                metrics: &metrics,
                gl_state: self.render_state.as_ref().unwrap(),
                zindex: 10,
            },
            &tabs,
        )?;

        computed.translate(euclid::vec2(
            0.,
            if self.config.tab_bar_at_bottom {
                self.dimensions.pixel_height as f32
                    - (computed.bounds.height() + border.bottom.get() as f32)
            } else {
                border.top.get() as f32
            },
        ));

        Ok(computed)
    }

    pub fn paint_fancy_tab_bar(&self) -> anyhow::Result<Vec<UIItem>> {
        let computed = self.fancy_tab_bar.as_ref().ok_or_else(|| {
            anyhow::anyhow!("paint_fancy_tab_bar called but fancy_tab_bar is None")
        })?;
        let ui_items = computed.ui_items();

        let gl_state = self.render_state.as_ref().unwrap();
        self.render_element(&computed, gl_state, None)?;

        Ok(ui_items)
    }
}

/// The pixel geometry of the fancy tab bar.
///
/// The tab bar model decides how many cells of title text each tab shows and
/// the renderer lays those tabs out in pixels; both have to agree about how
/// much room a tab has, so the arithmetic lives here and is used by both.
struct FancyTabBarGeometry {
    /// The cell that padding and margins are measured in
    cell_width: f32,
    cell_height: f32,
    /// One cell of title text, as the title font actually shapes it
    text_cell_width: f32,
    /// The full window width
    pixel_width: f32,
    /// Padding at the left of the tab strip
    left_padding: f32,
    /// The close button drawn at the right of each tab, if enabled
    close_button: f32,
    /// The most title cells that a tab is allowed to show
    tab_max_width: usize,
}

impl FancyTabBarGeometry {
    /// A blank cell held between the end of the title and the close button.
    /// Titles are measured in whole cells, but a glyph's ink can reach past
    /// the cell it advances by and fonts differ from platform to platform, so
    /// this is insurance against the last character of a title being clipped.
    fn title_gap(&self) -> f32 {
        self.text_cell_width
    }

    /// Everything a tab needs beyond its title text: 0.5 cells of padding
    /// either side, a 1px border either side, the blank cell that follows the
    /// title, and the close button (its poly, 0.25 cells of padding either
    /// side and 0.5 cells of left margin).
    fn tab_overhead(&self) -> f32 {
        self.cell_width + 2. + self.title_gap() + self.close_button
    }

    /// The width of a tab showing a title of the full tab_max_width cells
    fn desired_width(&self) -> f32 {
        (self.tab_max_width as f32 * self.text_cell_width) + self.tab_overhead()
    }

    /// The width of everything in the bar that is not a tab: the padding at
    /// the left of the strip, the new tab button, the status areas and any
    /// integrated window buttons.
    fn reserved(&self, new_tab_button: bool, status_cells: usize, window_buttons: usize) -> f32 {
        let mut reserved = self.left_padding;

        if new_tab_button {
            // The plus poly, 0.5 cells of padding either side, a 1px border
            // either side and 0.5 cells of left margin.
            reserved += (self.cell_height / 2.) + (2. * self.cell_width) + 2.;
        }

        // The status areas cost their text plus 0.5 cells of left padding
        // apiece.
        reserved += (status_cells as f32 * self.text_cell_width) + self.cell_width;

        // Integrated window buttons vary by style, so reserve a generous
        // 3 cells apiece.
        reserved += 3. * self.cell_width * window_buttons as f32;

        reserved
    }

    /// The width of a single tab. Tabs are given their full width while they
    /// fit, and share out whatever is really available once they do not.
    fn tab_width(&self, num_tabs: usize, reserved: f32) -> f32 {
        if num_tabs == 0 {
            return self.desired_width();
        }
        let available = (self.pixel_width - reserved).max(0.);
        self.desired_width().min(available / num_tabs as f32)
    }

    /// The width that a tab's title is clipped at. The title may reach into
    /// the blank cell that follows it, but never as far as the close button.
    fn title_width(&self, num_tabs: usize, reserved: f32) -> f32 {
        (self.tab_width(num_tabs, reserved) - self.tab_overhead() + self.title_gap()).max(0.)
    }

    /// The number of cells of title text that fit in a tab. Text is only
    /// rendered in whole cells, so this rounds down.
    fn title_cells(&self, num_tabs: usize, reserved: f32) -> usize {
        let width = self.tab_width(num_tabs, reserved);
        if width >= self.desired_width() {
            return self.tab_max_width;
        }
        let cells = ((width - self.tab_overhead()) / self.text_cell_width).floor();
        (cells.max(1.) as usize).min(self.tab_max_width)
    }
}

/// One cell of text as `font` actually shapes it. The cell width that a
/// font's metrics report is not always the width that its glyphs advance by,
/// and a title clipped against the wrong one loses its last character.
fn measure_cell_width(font: &Rc<LoadedFont>, metrics: &RenderMetrics) -> f32 {
    let fallback = metrics.cell_size.width as f32;
    match font.shape(
        "M",
        || {},
        BlockKey::filter_out_synthetic,
        None,
        wezterm_bidi::Direction::LeftToRight,
        None,
        None,
    ) {
        Ok(infos) => infos
            .first()
            .map(|info| info.x_advance.get() as f32)
            .unwrap_or(fallback),
        Err(_) => fallback,
    }
}

fn make_x_button(
    font: &Rc<LoadedFont>,
    metrics: &RenderMetrics,
    colors: &TabBarColors,
    tab_idx: usize,
    active: bool,
) -> Element {
    Element::new(
        &font,
        ElementContent::Poly {
            line_width: metrics.underline_height.max(2),
            poly: SizedPoly {
                poly: X_BUTTON,
                width: Dimension::Pixels(metrics.cell_size.height as f32 / 2.),
                height: Dimension::Pixels(metrics.cell_size.height as f32 / 2.),
            },
        },
    )
    // Ensure that we draw our background over the
    // top of the rest of the tab contents
    .zindex(1)
    .vertical_align(VerticalAlign::Middle)
    .float(Float::Right)
    .item_type(UIItemType::CloseTab(tab_idx))
    .hover_colors({
        let inactive_tab_hover = colors.inactive_tab_hover();
        let active_tab = colors.active_tab();

        Some(ElementColors {
            border: BorderColor::default(),
            bg: (if active {
                inactive_tab_hover.bg_color
            } else {
                active_tab.bg_color
            })
            .to_linear()
            .into(),
            text: (if active {
                inactive_tab_hover.fg_color
            } else {
                active_tab.fg_color
            })
            .to_linear()
            .into(),
        })
    })
    .padding(BoxDimension {
        left: Dimension::Cells(0.25),
        right: Dimension::Cells(0.25),
        top: Dimension::Cells(0.25),
        bottom: Dimension::Cells(0.25),
    })
    .margin(BoxDimension {
        left: Dimension::Cells(0.5),
        right: Dimension::Cells(0.),
        top: Dimension::Cells(0.),
        bottom: Dimension::Cells(0.),
    })
}
