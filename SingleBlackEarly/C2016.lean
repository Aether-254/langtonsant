import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2016 : checkSingleBlackFast2 (-76, -48) 17929 .west (31, 37) (-57, 14) = true := by
  decide +kernel

end LangtonsAnt
