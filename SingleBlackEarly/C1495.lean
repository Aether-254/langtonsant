import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1495 : checkSingleBlackFast (-28, -5) 12703 .west (1, 11) (-30, -9) = true := by
  decide +kernel

end LangtonsAnt
