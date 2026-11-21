import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1890 : checkSingleBlackFast2 (-63, -41) 16001 .west (19, 28) (-48, 8) = true := by
  decide +kernel

end LangtonsAnt
