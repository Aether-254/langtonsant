import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1565 : checkSingleBlackFast (-35, -11) 13119 .west (4, 15) (-34, -4) = true := by
  decide +kernel

end LangtonsAnt
