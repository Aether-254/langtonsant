import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1539 : checkSingleBlackFast (-32, -9) 12911 .west (3, 13) (-32, -7) = true := by
  decide +kernel

end LangtonsAnt
