import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1671 : checkSingleBlackFast (-44, -21) 13535 .west (9, 19) (-38, -1) = true := by
  decide +kernel

end LangtonsAnt
