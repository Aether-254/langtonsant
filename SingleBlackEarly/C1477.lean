import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1477 : checkSingleBlackFast (-27, -3) 12703 .west (0, 11) (-30, -8) = true := by
  decide +kernel

end LangtonsAnt
