import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1521 : checkSingleBlackFast (-31, -7) 12911 .west (2, 13) (-32, -6) = true := by
  decide +kernel

end LangtonsAnt
