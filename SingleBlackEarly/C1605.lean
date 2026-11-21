import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1605 : checkSingleBlackFast (-38, -15) 13223 .west (6, 16) (-35, -4) = true := by
  decide +kernel

end LangtonsAnt
