import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1573 : checkSingleBlackFast (-31, -13) 11072 .north (5, 0) (-31, -10) = true := by
  decide +kernel

end LangtonsAnt
