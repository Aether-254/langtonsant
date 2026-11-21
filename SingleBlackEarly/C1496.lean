import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1496 : checkSingleBlackFast2 (-28, -4) 12747 .west (1, 11) (-30, -9) = true := by
  decide +kernel

end LangtonsAnt
